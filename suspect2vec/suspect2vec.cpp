#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <vector>
#include <algorithm>

#define MAX_STRING 100
#define INIT_RANGE 0.1
#define sigmoid(x) 1/(1+exp(-(x)))

using namespace std;

int **data, *sample;
float **embed_in, *sample_vec, **embed_out, *update;
char infile[MAX_STRING], outfile[MAX_STRING];

int epochs = 2000, dim = 20;
float eta = 0.01, lambd = 0.1;

float rand_float() {
	return (float)rand() / (float)RAND_MAX;
}

void init_embeddings(int n)
{
	int i,j;
	for (i=0; i<n; i++) {
		for (j=0; j<dim; j++) {
			embed_in[i][j] = (rand_float()-0.5) / dim;
            embed_out[i][j] = 0;
		}
	}
}

void generate_sample(int i, int n)
{
	int j;
    int cnt;    
    do {
        cnt = 0;
        //float p = 0.3 + rand_float()*0.4;
        for (j=0; j<n; j++) {
            //sample[j] = data[i][j] && rand_float() > p;
            sample[j] = data[i][j] && rand_float() > 0.5;
            cnt += sample[j];
        }
    } while (cnt == 0);
}

void train(int m, int n)
{
    int iter,i,j,k;   
    int cnt;
    float score;
    int label;
    float loss, acc;
    
    for (iter=0; iter<epochs; iter++) {
        loss = 0, acc = 0;
        for (i=0; i<m; i++) {
            for (k=0; k<dim; k++)
                sample_vec[k] = 0;
            
            cnt = 0;
            generate_sample(i,n);
            for (j=0; j<n; j++) {
                cnt += sample[j];
                if (sample[j]) 
                    for (k=0; k<dim; k++)
                        sample_vec[k] += embed_in[j][k];
            }
            for (k=0; k<dim; k++)
                update[k] = 0;
            //assert(cnt > 0);
            for (k=0; k<dim; k++)
                sample_vec[k] /= cnt;
            
            for (j=0; j<n; j++) {
                score = 0;
                for (k=0; k<dim; k++)
                    score += sample_vec[k] * embed_out[j][k];
                score = sigmoid(score);
                label = data[i][j];                
                for (k=0; k<dim; k++) {
                    update[k] += embed_out[j][k] * (label-score);
                    embed_out[j][k] += eta * (sample_vec[k] * (label-score) - lambd * embed_out[j][k]);
                }
                acc += (score>0.5) == label;
                if (label)
                    loss -= log(score);
                else 
                    loss -= log(1-score);                
            }
            for (j=0; j<n; j++) {
                if (sample[j]) {
                    for (k=0; k<dim; k++)
                        embed_in[j][k] += eta * (update[k]/cnt - lambd * embed_in[j][k]);
                }
            }
        }
        if (iter%100 == 0) {
            printf("Epoch %d loss: %.4f\n",iter+1,loss/m);
            printf("accuracy: %.4f\n",acc/n/m);
            float mean_mag2 = 0;
            for (j=0; j<n; j++) {
                for (k=0; k<dim; k++)
                    mean_mag2 += embed_in[j][k]*embed_in[j][k];                
            }
            mean_mag2 /= n;
            printf("Mean squared vector magnitude: %f\n",mean_mag2);
        }
    }
}

int ArgPos(char *str, int argc, char **argv) {
  int a;
  for (a = 1; a < argc; a++) if (!strcmp(str, argv[a])) {
    if (a == argc - 1) {
      printf("Argument missing for %s\n", str);
      exit(1);
    }
    return a;
  }
  return -1;
}

int main(int argc, char **argv) {
	int i,j,k,m,n;
	FILE *fin, *fout;
	if (argc == 1) {
		printf("Suspect2vec training\n");
		printf("Parameters:\n");
		printf("\t-in <file>\n");
		printf("\t\tName of input file\n");
		printf("\t-out <file>\n");
		printf("\t\tName of output file\n");
		printf("\t-epochs <int>\n");
		printf("\t\tNumber of training epochs\n");
		printf("\t-dim <int>\n");
		printf("\t\tEmbedding dimension\n");
		printf("\t-eta <float>\n");
		printf("\t\tLearning rate\n");
		printf("\t-lambd <float>\n");
		printf("\t\tRegularization term\n");
		return 0;
	}

  	if ((i = ArgPos((char *)"-in", argc, argv)) > 0) strcpy(infile, argv[i + 1]);
  	if ((i = ArgPos((char *)"-out", argc, argv)) > 0) strcpy(outfile, argv[i + 1]);
	if ((i = ArgPos((char *)"-epochs", argc, argv)) > 0) epochs = atoi(argv[i + 1]);
	if ((i = ArgPos((char *)"-dim", argc, argv)) > 0) dim = atoi(argv[i + 1]);
	if ((i = ArgPos((char *)"-eta", argc, argv)) > 0) eta = atof(argv[i + 1]);
	if ((i = ArgPos((char *)"-lambd", argc, argv)) > 0) lambd = atof(argv[i + 1]);

	srand(0);

	fin = fopen(infile,"rb");
	if (fin == NULL) {
		printf("ERROR: input file not found!\n");
		exit(1);
	}
	fout = fopen(outfile,"wb");
	fscanf(fin,"%d %d",&m,&n);

	//TODO: check if malloc returns NULL
	embed_in = (float**) malloc(n * sizeof(float*));
	embed_out = (float**) malloc(n * sizeof(float*));
	data = (int**) malloc(m * sizeof(int*));
	sample = (int*) malloc(n * sizeof(int));
    sample_vec = (float*) malloc(dim * sizeof(float));
    update = (float*) malloc(dim * sizeof(float));
	for (i=0; i<m; i++) 
		data[i] = (int*) malloc(n*sizeof(int));
	for (i=0; i<n; i++) {
		embed_in[i] = (float*) malloc(dim*sizeof(float));
		embed_out[i] = (float*) malloc(dim*sizeof(float));
    }

    // read input data as 1-hot encoding of suspect sets
	for (i=0; i<m; i++) {
		for (j=0; j<n; j++) {
			fscanf(fin,"%d",&data[i][j]);
		}
	}

	init_embeddings(n);  
    train(m,n);
    
    // write embeddings to output     
    for (j=0; j<n; j++) {
        for (k=0; k<dim; k++)
            fprintf(fout,"%.6f ",embed_in[j][k]);
        fprintf(fout,"\n");
    }
    for (j=0; j<n; j++) {
        for (k=0; k<dim; k++)
            fprintf(fout,"%.6f ",embed_out[j][k]);
        fprintf(fout,"\n");
    }
    return 0;
}