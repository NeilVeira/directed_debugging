import random 
import numpy as np 
import collections


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
        
        
class NaivePrediction(object):
    def __init__(self):
        pass
        
    def fit(self, data):
        self.suspect_union = set([])
        for S in data:
            for s in S:
                self.suspect_union.add(s)
        sizes = [len(S) for S in data]
        self.size = int(np.median(sizes))
        
        self.cntx = collections.defaultdict(int)
        for S in data:
            for s in S:
                self.cntx[s] += 1
        
    def predict(self, sample, k=None, score_query=None):
        if k is None:
            k = self.size 
            
        all_suspects = self.suspect_union
        if score_query is not None:
            all_suspects = all_suspects.union(set(score_query))
        all_suspects = list(all_suspects)
        
        rank = list(sample)
        freqs = [(self.cntx[s],s) for s in all_suspects]
        freqs.sort(reverse=True)
        for _,s in freqs:
            if s not in rank:
                rank.append(s)
                
        ret = rank[:k]
                
        if score_query is not None:
            n = len(score_query)
            ret_scores = np.zeros(n)
            for i,s in enumerate(score_query):
                pos = rank.index(s) 
                ret_scores[i] = float(n - pos) / n                    
            return ret, ret_scores 
            
        else:
            return ret 
        
        