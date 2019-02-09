import numpy as np 
import scipy.optimize
import warnings 
warnings.filterwarnings('ignore')

class DATEPrediction(object):

    def __init__(self, prior_var=0.2):
        '''
        Initialize DATEPrediction object. 
        Parameters
        -------------
        prior_var:
            Variance to use for the Gaussian prior distribution. 
        '''
        self.prior_var = prior_var 
        self.map_weights = None
        self.M = 0
        
    def _precompute_MAP_weights(self, M):
        '''
        Precompute the MAP values for all possible (count(i), count(i,j)) values.
        M: number of training instances in the data 
        There are only O(M^2) different possible weights (since each count is between 0 and M)
        so it's much faster to precompute all of them than to compute it for each graph edge
        and for each training.
        '''
        self.M = M
        
        #compute binomial coefficients
        comb = np.zeros((M+1,M+1))
        for n in range(M+1):
            comb[n][0] = comb[n][n] = 1;
        for n in range(1,M+1):
            for r in range(1,n):
                comb[n][r] = comb[n-1][r] + comb[n-1][r-1]
        for n in range(M+1):
            for r in range(n+1):
                comb[n][r] = np.log(comb[n][r])
            
        mu = 0.5 
        prior = lambda x: -0.5*np.log(2*np.pi*self.prior_var) - 0.5*(x-mu)**2/self.prior_var
        self.map_weights = np.zeros((M+1,M+1))
        for n in range(M+1):
            for r in range(M+1):
                likelihood = lambda x: comb[int(n)][int(r)] + r*np.log(x) + (n-r)*np.log(1-x) 
                f = lambda x: -1* (prior(x) + likelihood(x))
                res = scipy.optimize.minimize_scalar(f, bounds=(0,1), method="bounded")
                self.map_weights[n][r] = res.x
                
    def fit(self, data):
        '''
        Compute n x n matrix of graph weights for the given data, where n is the total number of 
        suspects in existence. Each directed edge (a,b) the is probability P(b|a).
        data: iterable of suspect sets, where each suspect set is an iterable of hashable objects representing 
            individual suspects. 
        '''        
        # preprocessing to convert suspects in data to integers from 0..n-1
        self.suspect_union = set([])
        for suspect_set in data:
            self.suspect_union = self.suspect_union.union(set(suspect_set))
        self.suspect_union = list(self.suspect_union)
        n = len(self.suspect_union)
        
        self.suspect2id = dict(zip(self.suspect_union, range(n)))

        # compute MAP weights, if necessary
        if len(data) > self.M:
            self._precompute_MAP_weights(len(data))
        
        #count how many times each suspect is seen and how many times each pair 
        #of suspects is seen
        self.cnt_suspect = [0]*n
        cnt_pairs = [[0]*n for i in range(n)]
        for suspect_set in data:
            for s1 in suspect_set:
                i = self.suspect2id[s1]
                self.cnt_suspect[i] += 1
                for s2 in suspect_set:
                    j = self.suspect2id[s2]
                    cnt_pairs[i][j] += 1 
                    
        #build the graph
        self.weights = np.zeros((n,n))
        for i in range(n):
            for j in range(n):
                self.weights[i][j] = self.map_weights[self.cnt_suspect[i]][cnt_pairs[i][j]]
        
        
    def predict(self, sample, k=None, score_query=None):
        '''
        Predict remaining suspects in the sample suspect set. 
        Parameters
        -------------
        sample: 
            Iterable of suspects
        k: 
            Number of suspects to predict, including the length of the sample. If None, the number of 
            suspects is estimated using the stopping criterion. 
        score_query: list of suspects or None. If not None then also return an array of scores 
            for each item in score_query.         
        '''
        
        # Convert to ids, handling any new suspects
        n = len(self.suspect_union)
        for s in sample:
            if s not in self.suspect2id:
                self.suspect2id[s] = len(self.suspect2id)
                self.suspect_union.append(s)
        sample = [self.suspect2id[s] for s in sample]
            
        if len(self.suspect_union) > n:  
            # Update weights for new suspects 
            self.cnt_suspect.extend([0]*(len(self.suspect_union)-n))
            nn = len(self.suspect_union)
            new_weights = np.zeros((nn,nn))
            new_weights[:n,:n] = self.weights 
            for i in range(n,nn):
                for j in range(nn):
                    new_weights[i][j] = self.map_weights[0][0]      
            for i in range(n):
                for j in range(n,nn):
                    new_weights[i][j] = self.map_weights[self.cnt_suspect[i]][0]
            self.weights = new_weights 
            n = nn
        
        neg_logw = -1 * np.log(1-self.weights)
        ranking = sample
        
        all_scores = np.ones(len(ranking))
        
        #in_predicted[i] = 1 iff i is in the ranking
        in_predicted = [False]*n
        for i in ranking:
            in_predicted[i] = True 
        
        #neg_log_notp[i] = negative log of probability of not suspect i 
        #maximize neg_log_notp of suspect i <==> maximize probability of suspect i
        neg_log_notp = np.zeros(n)
        for j in ranking:
            neg_log_notp += neg_logw[j]
            
        #sort by negative log of 1-probability
        ordered_suspectz = []
        for i in range(n):
            if i not in ranking:
                ordered_suspectz.append((neg_log_notp[i], i))
                
        ordered_suspectz.sort()
        ordered_suspectz.reverse() 
        full_ranking = sample + [x[1] for x in ordered_suspectz] 
        
        if k is None:
            # Estimate k using the stopping criterion. 
            # Compute normalized scores
            scores = np.ones(n)
            for i in range(len(sample),n):
                scores[i] = 0
                for j in range(i):
                    scores[i] += neg_logw[full_ranking[j]][full_ranking[i]]      
            scores[len(sample):] /= np.max(scores[len(sample):])
            
            # Smooth the function
            smoothed_scores = np.ones(n)
            smooth_range = int(round(float(n)/60))
            for i in range(n):
                smoothed_scores[i] = np.mean(scores[max(0,i-smooth_range):i+smooth_range+1])
            
            # Find first local minimum as size estimate
            k = n
            min_hill_size = 2
            for i in range(len(sample),n-2):
                for j in range(min_hill_size):
                    if smoothed_scores[i+j] >= smoothed_scores[i+j+1]:
                        break 
                else:
                    k = i 
                    break
        
        k = min(k,n)
        for i in range(k-len(sample)):
            ranking.append(ordered_suspectz[i][1])
            
        # Convert back to suspects 
        ranking = [self.suspect_union[i] for i in ranking]
            
        if score_query:
            ret_scores = np.zeros(len(score_query))
            for i,s in enumerate(score_query):
                if s in self.suspect2id:
                    ret_scores[i] = neg_log_notp[self.suspect2id[s]]                
            return ranking, ret_scores
        else:
            return ranking 
