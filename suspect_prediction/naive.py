import random 
import numpy as np 

class RandomPrediction(object): 
    def __init__(self):
        pass
        
    def fit(self, data):
        self.suspect_union = set([])
        for S in data:
            for s in S:
                self.suspect_union.add(s)
        self.suspect_union = list(self.suspect_union)
        sizes = [len(S) for S in data]
        self.size = int(np.median(sizes))
        
        
    def predict(self, sample, k=None, score_query=None):
        random.shuffle(self.suspect_union)
        if k is None:
            k = self.size 
            
        rank = list(sample)
        for s in self.suspect_union:
            if s not in rank:
                rank.append(s) 
                
        ret = rank[:k]
                
        if score_query is not None:
            ret_scores = np.zeros(len(score_query))
            for i,s in enumerate(score_query):
                if s in rank:
                    pos = rank.index(s) 
                    ret_scores[i] = float(len(rank) - pos) / len(rank) 
                else:
                    assert s not in self.suspect_union
                    ret_scores[i] = 0 
            return ret, ret_scores 
                
        else:
            return ret 
        
