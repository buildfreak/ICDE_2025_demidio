# -*- coding: utf-8 -*-
"""
Created on Wed Mar 20 17:26:26 2024

@author: anonym
"""

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Aug 29 13:28:41 2023

@author: anonym
"""
    
#!/usr/bin/env python3
from itertools import islice
from networkit import graphtools 
import networkx as nx
import argparse
from heapq import heappush,heappop
import networkit as nk
from networkx.utils import pairwise
import time
from progress.bar import IncrementalBar, PixelBar

import os
from datetime import datetime
import csv
import matplotlib.pyplot as plt
import math
import statistics
from collections import deque
import sys


class PathException(Exception):
    """Base class for exceptions in Searching Paths."""
    
class NoPathException(PathException):
    """Exception for algorithms that should return a path when running
    on graphs where such a path does not exist."""
    
   
def read_nde(filename:str):
    with open(filename,'r', encoding='UTF-8') as f:
        
        grafo_ = nk.graph.Graph(weighted=False,directed=True)
        
        for line in f.readlines():
            edge = line.split(' ')
            grafo_.addEdge(int(edge[0]), int(edge[1]), addMissing=True)
    
        return grafo_
    
def read_hist(name):
    with open(name, "r", encoding='UTF-8') as fhandle:
        print("READING GRAPH:",name)
        firstline = True
        for line in fhandle:
            if firstline == True:
                fields = line.split(" ")
                firstline = False
                n = int(fields[0])
                m = int(fields[1])
                weighted = int(fields[2])==1
                directed = int(fields[3])==1
                graph = nk.graph.Graph(n,weighted,directed)
            else:
                fields = line.split(" ")
                graph.addEdge(int(fields[1]),int(fields[2]),int(fields[3]))
                    
        if not graph.numberOfEdges()==m:
            print(graph.numberOfEdges(),m)
            raise Exception('misreading of graph')
            
        wgraph = nk.graph.Graph(graph.numberOfNodes(),graph.isWeighted(),graph.isDirected())
        
        assert graph.numberOfNodes()==wgraph.numberOfNodes()
        if weighted==True:
            for vertice in range(graph.numberOfNodes()):
                for vicino in graph.iterNeighbors(vertice):
                    wgraph.addEdge(vertice,vicino,graph.weight(vertice,vicino))
        else:
            for vertice in range(graph.numberOfNodes()):
                for vicino in graph.iterNeighbors(vertice):
                    wgraph.addEdge(vertice,vicino)

        print("Read Graph:",name,"directed:",wgraph.isDirected(),"weighted:",wgraph.isWeighted())

        return wgraph

class yens_algorithm():

    def __init__(self, gr, kvalue):
        
        self.G = gr
        self.K = kvalue
        self.yens_skip_node = [False for _ in self.G.iterNodes()]
        self.yens_skip_edge = [False for _ in self.G.iterEdges()]
        self.yens_skip_node_trace = [0 for _ in self.G.iterNodes()]
        self.yens_skip_edge_trace = [0 for _ in range(kvalue*self.G.numberOfNodes())] #max edges to forbid
        self.yens_skip_node_cnt = 0
        self.yens_skip_edge_cnt = 0
        
        if self.G.isDirected():
            self.othersideNeighbors = self.G.iterInNeighbors
        else:
            self.othersideNeighbors = self.G.iterNeighbors
        
    def is_simple(self,path):
            
        assert len(path) > 0
        assert type(path)==tuple

        assert all(v in self.G.iterNeighbors(u) for u, v in pairwise(path))
    
        s_path = set()
        for el in path:
            if el in s_path:
                assert len(set(path)) < len(path)
                return False
            s_path.add(el)
        assert len(set(path)) == len(path)
        return True
    
    def yen_bidir_dijkstra(self,source,target):
        
        if self.yens_skip_node[source] or self.yens_skip_node[target]:
            raise NoPathException
            
        
        if target == source:
            return (0,(source,))
        
        Qf = []
        Qb = []
        Sf = set()
        Sb = set()
        df = {}
        db = {}
        pf = {}
        pb = {}
        
        heappush(Qf,(0,source))
        heappush(Qb,(0,target))
        df[source] = 0
        db[target] = 0
        pf[source] = -1
        pb[target] = -1
        
        best_d = sys.maxsize
        best_vertex = None
        
        while len(Qf)>0 and len(Qb)>0:
            du, u = heappop(Qf)            
            assert u in df
            Sf.add(u)
            dv, v = heappop(Qb)
            assert v in db
            Sb.add(v)
            
            for x in self.G.iterNeighbors(u):
                if self.yens_skip_node[x]:
                    continue
                if self.yens_skip_edge[self.G.edgeId(u,x)]:
                    continue
               
                if (x not in Sf) and (x not in df or df[x] > df[u] + self.G.weight(u, x)):
                    df[x] = df[u] + self.G.weight(u, x)
                    pf[x] = u
                    heappush(Qf,(df[x],x))
        
                if x in Sb and df[u] + self.G.weight(u, x) + db[x] < best_d:
                    best_d = df[u] + self.G.weight(u, x) + db[x]
                    best_vertex = x
                    
            for x in self.othersideNeighbors(v):
                if self.yens_skip_node[x]:
                    continue
                if self.yens_skip_edge[self.G.edgeId(x,v)]:
                    continue
                if (x not in Sb) and (x not in db or db[x] > db[v] + self.G.weight(x,v)):
                    db[x] = db[v] + self.G.weight(x,v)
                    pb[x] = v
                    heappush(Qb,(db[x],x))
        
        
                if x in Sf and db[v] + self.G.weight(x,v) + df[x] < best_d:
                    best_d = db[v] + self.G.weight(x,v) + df[x]
                    best_vertex = x
                    
            if df[u] + db[v] >= best_d:
                
                w = best_vertex
                
                path = deque([w])
                
                while pf[w]!=-1:
                    path.appendleft(pf[w])
                    w = pf[w]
                    
                w = best_vertex
        
                while pb[w]!=-1:
                    path.append(pb[w])
                    w = pb[w]
                    
                    
                
                path = tuple(path)
                assert self.is_simple(path)
                assert path[0]==source
                assert path[-1]==target
                assert best_vertex in path
                
                assert best_d == sum([self.G.weight(u,v) for u, v in pairwise(path)])
                del Qf[:]
                del Qb[:]
                del pf
                del pb
                del df 
                del db 
                del Sf
                del Sb
                return (best_d,path)  
            
        raise NoPathException(f"No path between {source} and {target}.")
            

    def yen_bidir_BFS(self, source, target):    
        
        pred, succ, w = self.yen_bidir_pred_succ(source, target)
        
        path = deque()

        while w is not None:
            path.append(w)
            w = succ[w]
    
    
        w = pred[path[0]]
        
        while w is not None:
            path.appendleft(w)
            w = pred[w]
            
        path=tuple(path)
        
        assert self.is_simple(path)
        
        del pred
        del succ
        return (len(path)-1,path)  
    
 
    


        # return tuple(path)
                
    def yen_bidir_pred_succ(self, source, target):
        

    
        if self.yens_skip_node[source] or self.yens_skip_node[target]:
            raise NoPathException
        if target == source:
            return ({target: None}, {source: None}, source)
    
    
        
        # predecesssor and successors in search
        pred = {source: None}
        succ = {target: None}
    
        # initialize fringes, start with forward
        forward_fringe = deque([source])
        reverse_fringe = deque([target])
        
        
        while forward_fringe and reverse_fringe:


            if len(forward_fringe) <= len(reverse_fringe):
                this_level = forward_fringe
                forward_fringe = deque()
                for v in this_level:
                    for w in self.G.iterNeighbors(v):
                        assert self.G.isDirected() or self.G.edgeId(v,w) == self.G.edgeId(w,v)
                        if self.yens_skip_edge[self.G.edgeId(v,w)]:
                            continue
                        if w==source or self.yens_skip_node[w]:
                            assert w not in succ
                            continue
                        if w not in pred:
                            forward_fringe.append(w)
                            pred[w] = v
                        if w in succ:
                            del forward_fringe
                            del reverse_fringe
                            return pred, succ, w
            else:
                this_level = reverse_fringe
                reverse_fringe = deque()
                for v in this_level:
                    for w in self.othersideNeighbors(v):
                        assert self.G.isDirected() or self.G.edgeId(v,w) == self.G.edgeId(w,v)
                        
                        if self.yens_skip_edge[self.G.edgeId(w,v)]:
                            continue
                        
                        if w==target or self.yens_skip_node[w]:
                            assert w not in pred
                            continue
                        if w not in succ:
                            succ[w] = v
                            reverse_fringe.append(w)
                        if w in pred:
                            del forward_fringe
                            del reverse_fringe
                            return pred, succ, w
        del forward_fringe
        del reverse_fringe
        
        raise NoPathException(f"No path between {source} and {target}.")
        
    def equals(self,P,ind,L):
        i = 0
        
        assert len(L)==ind

        while i < len(L):
            if P[i]!=L[i]:
                assert P[:ind] != L
                return False
            i+=1
            
        assert P[:ind] == L
        return True
        
        
    def run(self, source, target):
        
        results = []        
        yen_PQ = []
        yen_paths = set()
        
        assert all(not self.yens_skip_node[v] for v in self.G.iterNodes())
        assert all(not self.yens_skip_edge[self.G.edgeId(u, v)] for u,v in self.G.iterEdges())          
            
        if self.G.isWeighted():
            self.yen_shortest_paths = self.yen_bidir_dijkstra
        else:
            self.yen_shortest_paths = self.yen_bidir_BFS
            
        try:
            pobj = self.yen_shortest_paths(source,target)
            p = pobj[1]
            
            assert p[0]==source
            assert p[-1]==target            
            assert p not in yen_paths
            
            heappush(yen_PQ,pobj)
            yen_paths.add(p)
            
            
        except NoPathException:
            return results
        
        
        except Exception as err:
            print(f"Unexpected {err=}, {type(err)=}")
            raise
            
    
        while len(yen_PQ)>0:
    
            element  = heappop(yen_PQ)
            
            assert element[1][0]==source
            assert element[1][-1]==target
            
            assert type(element[1])==tuple
            
            results.append(element)
            
            assert sorted(results,key=lambda x:x[0])==results
            
            if len(results)==self.K:
                del yen_PQ[:]
                del yen_PQ
                yen_paths.clear()
                return results
          
            assert all(not self.yens_skip_node[v] for v in self.G.iterNodes())
            assert all(not self.yens_skip_edge[self.G.edgeId(u, v)] for u,v in self.G.iterEdges())          
                  

            index = 1    
            
            
            while index < len(element[1]):
                
                l_root = element[1][:index]
                
                assert type(l_root)==tuple
                
                for pobj in results:
                    
                    path = pobj[1]
                    assert type(path)==tuple
                    
                    if self.equals(path,index,l_root):
                        eid = self.G.edgeId(path[index - 1], path[index])
                        if not self.yens_skip_edge[eid]:
                            self.yens_skip_edge[eid]=True
                            self.yens_skip_edge_trace[self.yens_skip_edge_cnt] = eid
                            self.yens_skip_edge_cnt+=1
                                          
                index+=1        
                
                try:
                    assert all(v in self.G.iterNeighbors(u) for u, v in pairwise(l_root[:-1]))

                    output = self.yen_shortest_paths(l_root[-1],target)   
                    pgt = output[1]
                    peso = output[0]

                    assert all(v in self.G.iterNeighbors(u) for u, v in pairwise(pgt))                    

                    
                    new_path = l_root[:-1] + pgt     
                                   
                    assert new_path[0]==source and new_path[-1]==target                    
                    assert self.is_simple(new_path)   
    
                    if new_path in yen_paths:
                        
                        if not self.yens_skip_node[l_root[-1]]:
                            self.yens_skip_node[l_root[-1]]=True
                            self.yens_skip_node_trace[self.yens_skip_node_cnt] = l_root[-1]
                            self.yens_skip_node_cnt+=1
                            
                        del new_path

                        continue

                    edge_gap = 0 if len(l_root)==1 else self.G.weight(l_root[-2],l_root[-1])            
                    new_weight = peso + sum([self.G.weight(u,v) for u, v in pairwise(l_root[:-1])]) + edge_gap                     
                    assert new_weight == sum([self.G.weight(u,v) for u, v in pairwise(new_path)])
                    
                    cobj = (new_weight,new_path)
                    heappush(yen_PQ,cobj)                
                    yen_paths.add(new_path)
    
                except NoPathException:
                    pass
                
                except Exception as err:
                    print(f"Unexpected {err=}, {type(err)=}")
                    raise
                    
                if not self.yens_skip_node[l_root[-1]]:
                    self.yens_skip_node[l_root[-1]]=True
                    self.yens_skip_node_trace[self.yens_skip_node_cnt] = l_root[-1]
                    self.yens_skip_node_cnt+=1
            
            cnt = 0
            while cnt < self.yens_skip_node_cnt:
                x = self.yens_skip_node_trace[cnt]
                assert self.yens_skip_node[x]
                self.yens_skip_node[x]=False
                cnt+=1

                
            cnt = 0
            while cnt < self.yens_skip_edge_cnt:
                e_id = self.yens_skip_edge_trace[cnt]
                assert self.yens_skip_edge[e_id]
                self.yens_skip_edge[e_id]=False
                cnt+=1

                
            self.yens_skip_node_cnt = 0
            self.yens_skip_edge_cnt = 0
            
    
        del yen_PQ[:]
        del yen_PQ       
        yen_paths.clear()       
        return results
        
    

    



def test_equality(flag, array_A, array_B):
    
    assert flag == "YY" or flag =="BY"
    
    if flag == "BY":
        array_sstopk = array_A
        array_yen = array_B
       
       
        assert all(type(i)==tuple for i in array_sstopk)
        assert all(type(i)==tuple for i in array_yen)
        
        if len([i[1] for i in array_sstopk])!=len(set([i[1] for i in array_sstopk])):
            raise Exception('uniqueness exception')
            
        if len(array_yen)!=len(array_sstopk):
            
            print("YE",len(array_yen))
            print("SS",len(array_sstopk))   
            
            for i in range(min(len(array_yen),len(array_sstopk))):
                if array_yen[i]==array_sstopk[i] or array_yen[i].weight==array_sstopk[i].weight:
                    print(i,"correct",array_yen[i],array_sstopk[i])
                else:
                    print(i,"mismatch",array_yen[i],array_sstopk[i])
            for i in [x for x in array_yen if x not in array_sstopk]:
                    print("missing",i)
            raise Exception('card exception')
            
        indice = 0
        for indice in range(len(array_yen)):
            if array_yen[indice][0]!=array_sstopk[indice][0]:
                for xy in array_yen:
                    print("YEN",array_yen.index(xy),xy)
                for xy in array_sstopk:
                    print("SSTOP",array_sstopk.index(xy),xy)

                print("index",indice)
                print(array_yen[indice],"Y")  
                print(array_sstopk[indice],"B")  
                
                raise Exception('correctness exception')
                
    else:
        array_yen_custom = array_A
        array_yen = array_B
        assert all(type(i)==tuple for i in array_yen_custom)
        assert all(type(i)==tuple for i in array_yen)
        
        if len([i[1] for i in array_yen_custom])!=len(set([i[1] for i in array_yen_custom])):
            raise Exception('uniqueness exception')
            
        if len(array_yen)!=len(array_yen_custom):
            print("Y",len(array_yen))
            print("Ycustom",len(array_yen_custom))   
            for i in range(min(len(array_yen),len(array_yen_custom))):
                if array_yen[i]==array_yen_custom[i] or array_yen[i].weight==array_yen_custom[i].weight:
                    print(i,"correct",array_yen[i],array_yen_custom[i])
                else:
                    print(i,"mismatch",array_yen[i],array_yen_custom[i])
                    
            for i in [x for x in array_yen if x not in array_yen_custom]:
                    print("missing",i)
            
            raise Exception('card exception')
            
        indice = 0
        for indice in range(len(array_yen)):
            if array_yen[indice][0]!=array_yen_custom[indice][0]:
                print("Y",array_yen)
                print("Ycustom",array_yen_custom)    
                print("Y",array_yen[indice])
                print("Ycustom",array_yen_custom[indice])  
                
               
                raise Exception('correctness exception')
                
class single_source_top_k():

    def __init__(self, grph, num_k, r):
        
        self.graph = grph
        self.kappa = num_k
        self.pruned_visits = 0
        self.extra_visits = 0
        self.num_yen_calls = 0
        
        
        self.top_k = [deque() for _ in self.graph.iterNodes()]        
        self.predecessors = [None for _ in self.graph.iterNodes()]        
        self.ignore_nodes = [False for _ in self.graph.iterNodes()]        
        
        self.supersaturated = [False for _ in self.graph.iterNodes()]
        self.done = [False for _ in self.graph.iterNodes()]

        
        self.valutati = [False for _ in self.graph.iterNodes()]
        self.valutati_trace = [0 for _ in self.graph.iterNodes()]
        self.valutati_count = 0

        
        self.sstopk_skip_node = [False for _ in self.graph.iterNodes()]
        self.sstopk_skip_node_trace = [0 for _ in self.graph.iterNodes()]
        self.sstopk_skip_node_cnt = 0


        self.sstopk_skip_edge = [False for _ in self.graph.iterEdges()]        
        self.sstopk_skip_edge_trace = [0 for _ in range(self.kappa*self.graph.numberOfNodes())] #max edges to forbid
        self.sstopk_skip_edge_cnt = 0
        
        self.unsaturated = [True for v in self.graph.iterNodes()]
        
        self.number_of_non_sat = self.graph.numberOfNodes()-1

        self.root = r
        
        self.unsaturated[r] = False        
        self.supersaturated[r] = True        
        
        if self.graph.isWeighted():
            self.shortest_paths = self.bidir_dijkstra
        else:
            self.shortest_paths = self.bidir_BFS
        
        self.PQ =  []  
        self.PQ_trace = [set() for _ in self.graph.iterEdges()]  
        
        if self.graph.isDirected():
            self.othersideNeighbors = self.graph.iterInNeighbors
        else:
            self.othersideNeighbors = self.graph.iterNeighbors
        
        
    def deallocation(self):

        for i in self.PQ:
            del i
        
        del self.PQ
        
        
        del self.PQ_trace[:]
        del self.PQ_trace
        
        del self.ignore_nodes[:]
        del self.ignore_nodes

        del self.supersaturated[:]
        del self.supersaturated
        
        del self.valutati[:]
        del self.valutati

        del self.valutati_trace[:]
        del self.valutati_trace
        
        del self.sstopk_skip_node[:]
        del self.sstopk_skip_node
        
        del self.sstopk_skip_node_trace[:]
        del self.sstopk_skip_node_trace
        
        del self.sstopk_skip_edge[:]
        del self.sstopk_skip_edge

        del self.sstopk_skip_edge_trace[:]
        del self.sstopk_skip_edge_trace


                
        assert self.number_of_non_sat == len([i for i in self.unsaturated if i==True])
        assert self.number_of_non_sat == len([v for v in self.graph.iterNodes() if self.unsaturated[v]])
        
        assert self.number_of_non_sat == len([v for v in self.graph.iterNodes() if len(self.top_k[v])<self.kappa and v!=self.root])
        
        del self.unsaturated[:]
        del self.unsaturated    
        



    

    def enqueue(self,ver,tupla_cammino):
        
        assert not self.supersaturated[ver]
        assert tupla_cammino not in self.top_k[ver]        
        
        if tupla_cammino[1] in self.PQ_trace[ver]:
            assert tupla_cammino in self.PQ                
            return
        else:
            assert tupla_cammino not in self.PQ
            assert tupla_cammino[1] not in self.PQ_trace[ver]
            assert tupla_cammino not in self.top_k[ver]

            heappush(self.PQ,tupla_cammino)
            
            self.PQ_trace[ver].add(tupla_cammino[1])





    def algo_sstopk(self):
        

        assert type(self.top_k)==list and all(len(self.top_k[v])==0 for v in self.graph.iterNodes())     
        
        assert type(self.unsaturated)==list        
        
        estrazioni = 0

        print("SSTopk for root:",self.root,"PQ:",len(self.PQ),"estrazioni:",estrazioni,"Non sat:",self.number_of_non_sat,"Yen calls:",self.num_yen_calls,"...",end="",flush=True)

        assert not self.unsaturated[self.root]

        for ngx in self.graph.iterNeighbors(self.root):
            
            cobj = (self.graph.weight(self.root,ngx),(self.root,ngx))

            self.enqueue(ver=ngx,tupla_cammino=cobj)

            assert self.unsaturated[ngx]
            
            
        while len(self.PQ)>0:
            
            estrazioni+=1

            if estrazioni%100000==0:
                print("\nSSTopk for root:",self.root,"PQ:",len(self.PQ),"estrazioni:",estrazioni,"Non sat:",self.number_of_non_sat,"Yen calls:",self.num_yen_calls,"...",end="",flush=True)
                
            
            elemento =  heappop(self.PQ)     
            wptx = elemento[0]
            ptx = elemento[1]
            assert type(ptx)==tuple        
            
            assert wptx == sum([self.graph.weight(u,v) for u, v in pairwise(ptx)])
            
            
            assert ptx[0]==self.root
            assert ptx[-1]!=self.root
            
            assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(ptx))
            
            assert self.number_of_non_sat>0
            
            assert elemento not in self.top_k[ptx[-1]]
          
            vtx = ptx[-1]
            
            assert ptx in self.PQ_trace[vtx]
            
            self.PQ_trace[vtx].remove(ptx)

            if len(self.top_k[vtx]) < self.kappa:
                                
                self.standard(vtx,elemento)    

                del ptx
                
                if self.number_of_non_sat==0:
                    print("\nSSTopk for root:",self.root,"PQ:",len(self.PQ),"estrazioni:",estrazioni,"Non sat:",self.number_of_non_sat,"Yen calls:",self.num_yen_calls,"...",end="",flush=True)

                    return
                
                continue
            
            else:
                assert self.number_of_non_sat>0
                assert not self.unsaturated[vtx]

                self.beyond(vtx,elemento)
                
                assert self.number_of_non_sat>0
                del ptx
                

        print("\nSSTopk for root:",self.root,"PQ:",len(self.PQ),"estrazioni:",estrazioni,"Non sat:",self.number_of_non_sat,"Yen calls:",self.num_yen_calls,"...",end="",flush=True)



    def add_pred(self,dst):
        
        assert not self.unsaturated[dst]

        assert self.predecessors[dst] is None or self.done[dst] 

        if self.done[dst]:

            assert self.predecessors[dst] is not None
            return
        
        assert self.predecessors[dst] is None
        self.predecessors[dst] = set()

        for r_dst in self.top_k[dst]:
            r_dst_path = r_dst[1]
            assert r_dst_path[0]==self.root
            assert r_dst_path[-1]==dst
            
            assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(r_dst_path))
        
            l = 1
            while l<len(r_dst_path)-1:
                u = r_dst_path[l]
                self.predecessors[dst].add(u)
                l+=1               
        assert dst not in self.predecessors[dst]
        assert self.root not in self.predecessors[dst]
   
    def add_pred_by_external_paths(self,dst,SR_):
        
        assert self.predecessors[dst] is None
        self.predecessors[dst] = set()
        
        assert self.unsaturated[dst]
        assert not self.done[dst]

            

        for r_dst in self.top_k[dst]:
            r_dst_path = r_dst[1]

            assert r_dst_path[0]==self.root
            assert r_dst_path[-1]==dst
            assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(r_dst_path))
            assert r_dst_path[0]==self.root
            assert r_dst_path[-1]==dst
            
            assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(r_dst_path))
            
            l = 1
            while l<len(r_dst_path)-1:
                u = r_dst_path[l]
                self.predecessors[dst].add(u)
                l+=1 
            assert dst not in self.predecessors[dst]
            assert self.root not in self.predecessors[dst]
            
            for m_dst in SR_:
                m_dst_path = m_dst[1]
                assert m_dst_path[0]==self.root
                assert m_dst_path[-1]==dst
                assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(m_dst_path))
                assert m_dst not in self.top_k[dst]


                l = 1
                while l<len(m_dst_path)-1:
                    u = m_dst_path[l]
                    self.predecessors[dst].add(u)
                    l+=1 
            assert dst not in self.predecessors[dst]
            assert self.root not in self.predecessors[dst]

        
    def standard(self,VERT,EL):
        
        assert len(self.top_k[VERT])<self.kappa
        
        WPATH, PPATH = EL
        
        assert self.unsaturated[VERT]
         
        assert type(PPATH)==tuple
        
        assert (WPATH,PPATH) not in self.top_k[VERT]
        
        self.top_k[VERT].append((WPATH,PPATH))       

        assert list(self.top_k[VERT])==sorted(self.top_k[VERT],key=lambda x: x[0])    
        assert len(self.top_k[VERT])<=self.kappa
        
        

        
        
        if len(self.top_k[VERT])==self.kappa:  
            
            assert self.unsaturated[VERT]   
            
            self.unsaturated[VERT] = False
            
            self.number_of_non_sat -= 1

            self.add_pred(dst=VERT)

            
            assert(len([val for val in self.unsaturated if val==True])==self.number_of_non_sat)
            
            if self.number_of_non_sat==0:
                return
            


        assert (self.graph.isDirected() and PPATH[-2] in self.graph.iterInNeighbors(VERT)) or (PPATH[-2] in self.graph.iterNeighbors(VERT))
        
        
        assert self.number_of_non_sat>0
        
        self.init_avoidance(PPATH)
        
        for ngx in self.graph.iterNeighbors(VERT):
            
            if self.ignore_nodes[ngx]:
                continue
            if self.supersaturated[ngx]:
                continue
            
            assert ngx not in PPATH
            assert ngx != self.root
            
            
            cobj = (WPATH+self.graph.weight(VERT,ngx),PPATH+(ngx,))
            self.enqueue(ver=ngx, tupla_cammino=cobj)
                
                
            
        self.clean_avoidance(PPATH)



    def equals(self,P,ind,L):
        i = 0
        
        assert len(L)==ind

        while i < len(L):
            if P[i]!=L[i]:
                assert P[:ind] != L
                return False
            i+=1
            
        assert P[:ind] == L
        return True
    def getMissingByYen(self,s,t):
        
        PQ = []
        PQ_paths = set()
        res = []
        
        self.num_yen_calls += 1
                    
        

        try:
            pobj = self.shortest_paths(s,t)
            alt_p = pobj[1]
            assert  pobj[0] == sum([self.graph.weight(u,v) for u, v in pairwise(alt_p)])

            assert alt_p[0]==s
            assert alt_p[-1]==t
            assert alt_p not in PQ_paths
            
            heappush(PQ,pobj)
            PQ_paths.add(alt_p)
            
        except NoPathException:
            pass
        
        except Exception as err:
            print(f"Unexpected {err=}, {type(err)=}")
            raise
                
        while len(PQ)>0:            
            
            pdet_object  = heappop(PQ)
            
            P_det = pdet_object[1]

            assert P_det[0]==s
            assert P_det[-1]==t            
            assert len(res)<self.kappa

            assert pdet_object not in res
            
            res.append(pdet_object)
            
            assert sorted(res,key=lambda x:x[0])==list(res)

            if len(res)==self.kappa:
               break
           
            index = 1    
           
            while index < len(P_det):
               
               l_root = P_det[:index]
               
               assert type(l_root)==tuple
               
               for res_obj in res:
                   path = res_obj[1]
                   
                   assert type(path)==tuple
                   if self.equals(path,index,l_root):
                   # if path[:index] == l_root:
                       eid = self.graph.edgeId(path[index - 1], path[index])
                       
                       if not self.sstopk_skip_edge[eid]:
                           self.sstopk_skip_edge[eid]=True
                           self.sstopk_skip_edge_trace[self.sstopk_skip_edge_cnt] = eid
                           self.sstopk_skip_edge_cnt+=1
                                         
               index+=1         
               
               try:
                   
                   assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(l_root[:-1]))

                   pgt_obj = self.shortest_paths(l_root[-1],t)
                   pgt = pgt_obj[1]
                   pes = pgt_obj[0]
                   assert pes == sum([self.graph.weight(u,v) for u, v in pairwise(pgt)])
                   assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(pgt))


                   
                   new_path = l_root[:-1] + pgt
                   
                   assert new_path[0]==s and new_path[-1]==t
                   assert self.is_simple(new_path)   
   
                   if new_path in PQ_paths:
                       if not self.sstopk_skip_node[l_root[-1]]:
                           self.sstopk_skip_node[l_root[-1]]=True
                           self.sstopk_skip_node_trace[self.sstopk_skip_node_cnt] = l_root[-1]
                           self.sstopk_skip_node_cnt+=1
                       del new_path
                       continue
                   
                   edge_gap = 0 if len(l_root)==1 else self.graph.weight(l_root[-2],l_root[-1])
                   new_weight = pes+sum([self.graph.weight(u,v) for u, v in pairwise(l_root[:-1])])+edge_gap 
                   assert new_weight == sum([self.graph.weight(u,v) for u, v in pairwise(new_path)])
                   cobj = (new_weight,new_path)

                   heappush(PQ,cobj)
                   
                   PQ_paths.add(new_path)
   
               except NoPathException:
                   pass
               
               except Exception as err:
                   print(f"Unexpected {err=}, {type(err)=}")
                   raise
                   
               if not self.sstopk_skip_node[l_root[-1]]:
                   self.sstopk_skip_node[l_root[-1]]=True
                   self.sstopk_skip_node_trace[self.sstopk_skip_node_cnt] = l_root[-1]
                   self.sstopk_skip_node_cnt+=1
           
            
            cnt = 0
            while cnt < self.sstopk_skip_node_cnt:
                x = self.sstopk_skip_node_trace[cnt]
                assert self.sstopk_skip_node[x]
                self.sstopk_skip_node[x]=False
                cnt+=1
            cnt = 0
            while cnt < self.sstopk_skip_edge_cnt:
                e_id = self.sstopk_skip_edge_trace[cnt]
                assert self.sstopk_skip_edge[e_id]
                self.sstopk_skip_edge[e_id]=False
                cnt+=1
    
               
            self.sstopk_skip_node_cnt = 0
            self.sstopk_skip_edge_cnt = 0
            
        del PQ[:]
        del PQ
        PQ_paths.clear()
        del PQ_paths
        return res
        



        
        
    def beyond(self,VERT,EL):
        
        self.extra_visits += 1
        
        assert self.number_of_non_sat>0
        WPATH, PPATH = EL
        assert not self.unsaturated[VERT] 
        assert len(self.top_k[VERT])>=self.kappa 
        assert EL not in self.top_k[VERT] 
        
        assert type(PPATH) == tuple
        
        assert PPATH[0]==self.root and PPATH[-1]==VERT

        if self.graph.degree(VERT)<=1:
            self.supersaturated[VERT] = True

        if self.supersaturated[VERT]:
            self.pruned_visits += 1
            return


        
        external_Q = deque()
        
        assert all(not self.valutati[x] for x in self.graph.iterNodes())        
        
        
        self.valutati[VERT] = True
        self.valutati_trace[self.valutati_count] = VERT
        self.valutati_count += 1
        
        self.valutati[self.root] = True
        self.valutati_trace[self.valutati_count] = self.root
        self.valutati_count += 1
        
        external_Q.append(VERT)

        if __debug__:
            ASv = []
            


        
        while len(external_Q)>0:
            
            v = external_Q.popleft()
            
            
            if __debug__:
                assert v not in ASv
                ASv.append(v)
                
            assert v is not self.root
            assert self.valutati[v]
            assert self.valutati_count<=self.graph.numberOfNodes()
            
            assert not self.supersaturated[v]
            
            assert v is not self.root           

            
            if self.unsaturated[v]: 

                assert not self.done[v]
                    
                SR = self.getMissingByYen(s=self.root,t=v)
                
                assert len(SR)<=self.kappa
                
                if len(self.top_k[v]) > 0:
                    assert len
                    ct = 0
                    while ct < len(SR):
                        el = SR[ct]
                        w_el = el[0]
                        if w_el<self.top_k[v][-1][0]:
                            #all those strictly shorter than the heaviest found so far are necessarily in 
                            assert el in self.top_k[v]
                            assert ct==0
                            SR.pop(ct)
                            continue
                        
                        elif w_el==self.top_k[v][-1][0]:
                            
                            inner_counter = len(self.top_k[v])-1
                            trovato = False
                            while inner_counter>=0:
                                inner_el = self.top_k[v][inner_counter]
                                w_inner_el = inner_el[0]
                                if w_inner_el != w_el:
                                    assert w_inner_el<w_el
                                    break
                                if el == inner_el:
                                    assert el in self.top_k[v]
                                    trovato = True
                                    break
                                else:
                                    inner_counter-=1
                                    
                            if trovato:
                                assert el in self.top_k[v]
                                SR.pop(ct)
                                assert el not in SR
                                continue

                            else:
                                assert el not in self.top_k[v]
                                assert el in SR
                                ct+=1

                                    


                        else:
                            assert w_el>self.top_k[v][-1][0]
                            assert all (SR[ux] not in self.top_k[v] for ux in range(ct,len(SR)))
                            break
                                        
                while len(SR)+len(self.top_k[v])>self.kappa:
                    SR.pop(-1)
                    
                assert len(SR)+len(self.top_k[v])<=self.kappa
                
                
                self.add_pred_by_external_paths(dst=v,SR_=SR)
                
                for el in SR:
                    assert el not in self.top_k[v]
                    self.enqueue(ver=v, tupla_cammino=el)
                   
                    
                self.done[v] = True

                assert not self.supersaturated[v]

                
                        
                del SR[:]
                del SR

                

            assert self.predecessors[v] is not None
            
            for x in self.predecessors[v]:
                
                if self.supersaturated[x]:
                    continue
                                
                if not self.valutati[x]:
                    self.valutati[x] = True
                    self.valutati_trace[self.valutati_count] = x
                    self.valutati_count += 1
                    assert x not in external_Q
                    assert x is not VERT     
                    
                    external_Q.append(x)
                
            
            
            self.supersaturated[v] = True

                

            
        del external_Q
       
        cnt = 0
        
        while cnt < self.valutati_count:
              el = self.valutati_trace[cnt]
              assert self.valutati[el]
              self.valutati[el]=False
              cnt+=1
             
        self.valutati_count = 0    
        assert self.supersaturated[VERT] 
        
  
        
    def init_avoidance(self,avoid):        

        assert avoid[0]==self.root        

        for u in avoid[:-1]:
            assert not self.ignore_nodes[u]
            self.ignore_nodes[u]=True
  
            
    def clean_avoidance(self,avoid):
        
        assert avoid[0]==self.root        
        for u in avoid[:-1]:    
            assert self.ignore_nodes[u]
            self.ignore_nodes[u]=False
     
                
        
   
    def is_simple(self,path):
            
        assert len(path) > 0
        assert type(path)==tuple
        assert all(v in self.graph.iterNeighbors(u) for u, v in pairwise(path))

        s_path = set()
        for el in path:
            if el in s_path:
                assert len(set(path)) < len(path)
                return False
            s_path.add(el)
        assert len(set(path)) == len(path)
        return True
       
    
    def bidir_dijkstra(self, source, target):
        
        
   
        
            
        if self.sstopk_skip_node[source] or self.sstopk_skip_node[target]:
            raise NoPathException
            
        
        if target == source:
            return (0,(source,))

        # local_priority = []
        # heappush(local_priority, (starting_path.weight,starting_path))
        
        # seen = set()

        # while len(local_priority)>0:
            
        #     w_p, p_obj  = heappop(local_priority)
        #     assert type(p_obj)==myPath

        #     p = p_obj.path_tuple
        #     v = p[-1]
        #     seen.add(v)
        #     assert source in seen
        #     if v == target:
        #         return p_obj
            
        #     for w in self.graph.iterNeighbors(v):
        #         assert self.graph.edgeId(v,w) == self.graph.edgeId(w,v) or self.graph.isDirected()
                
        #         if self.sstopk_skip_edge[self.graph.edgeId(v,w)]:
        #             continue
        #         if w in seen or self.sstopk_skip_node[w]:
        #             continue
        #         new_p_obj =  myPath(path_tuple=p+(w,),weight=p_obj.weight+self.graph.weight(v,w))
        #         heappush(local_priority, (new_p_obj.weight,new_p_obj))
        Qf = []
        Qb = []
        Sf = set()
        Sb = set()
        df = {}
        db = {}
        pf = {}
        pb = {}
        
        heappush(Qf,(0,source))
        heappush(Qb,(0,target))
        df[source] = 0
        db[target] = 0
        pf[source] = -1
        pb[target] = -1
        
        best_d = sys.maxsize
        best_vertex = None
        
        while len(Qf)>0 and len(Qb)>0:
            du, u = heappop(Qf)            
            assert u in df
            Sf.add(u)
            dv, v = heappop(Qb)
            assert v in db
            Sb.add(v)
            
            for x in self.graph.iterNeighbors(u):
                if self.sstopk_skip_node[x]:
                    continue
                if self.sstopk_skip_edge[self.graph.edgeId(u,x)]:
                    continue
               
                if (x not in Sf) and (x not in df or df[x] > df[u] + self.graph.weight(u, x)):
                    df[x] = df[u] + self.graph.weight(u, x)
                    pf[x] = u
                    heappush(Qf,(df[x],x))

                if x in Sb and df[u] + self.graph.weight(u, x) + db[x] < best_d:
                    best_d = df[u] + self.graph.weight(u, x) + db[x]
                    best_vertex = x
                    
            for x in self.othersideNeighbors(v):
                if self.sstopk_skip_node[x]:
                    continue
                if self.sstopk_skip_edge[self.graph.edgeId(x,v)]:
                    continue
                if (x not in Sb) and (x not in db or db[x] > db[v] + self.graph.weight(x,v)):
                    db[x] = db[v] + self.graph.weight(x,v)
                    pb[x] = v
                    heappush(Qb,(db[x],x))


                if x in Sf and db[v] + self.graph.weight(x,v) + df[x] < best_d:
                    best_d = db[v] + self.graph.weight(x,v) + df[x]
                    best_vertex = x
                    
            if df[u] + db[v] >= best_d:
                
                w = best_vertex
                
                path = deque([w])
                
                while pf[w]!=-1:
                    path.appendleft(pf[w])
                    w = pf[w]
                    
                w = best_vertex

                while pb[w]!=-1:
                    path.append(pb[w])
                    w = pb[w]
                    
                    
                
                path = tuple(path)
                assert self.is_simple(path)
                assert path[0]==source
                assert path[-1]==target
                assert best_vertex in path
                
                assert best_d == sum([self.graph.weight(u,v) for u, v in pairwise(path)])
                del Qf[:]
                del Qb[:]
                del pf
                del pb
                del df 
                del db 
                del Sf
                del Sb
                return (best_d,path)
            
        raise NoPathException(f"No path between {source} and {target}.")

        
    def bidir_BFS(self, source, target):
    
    
        pred, succ, w = self.bidir_pred_succ(source, target)
        
        path = deque()
        while w is not None:
            path.append(w)
            w = succ[w]
            
    
    
        w = pred[path[0]]
        
        while w is not None:
            path.appendleft(w)
            w = pred[w]
            
        path=tuple(path)
        assert self.is_simple(path)
        return (len(path)-1,path)
                
    def bidir_pred_succ(self, source, target):
        

    
        if self.sstopk_skip_node[source] or self.sstopk_skip_node[target]:
            raise NoPathException
        if target == source:
            return ({target: None}, {source: None}, source)
    
    
        
        # predecesssor and successors in search
        pred = {source: None}
        succ = {target: None}
    
        # initialize fringes, start with forward
        forward_fringe = deque([source])
        reverse_fringe = deque([target])
        
        
        while forward_fringe and reverse_fringe:
  

            if len(forward_fringe) <= len(reverse_fringe):
                this_level = forward_fringe
                forward_fringe = deque()
                for v in this_level:
                    for w in self.graph.iterNeighbors(v):
                        assert self.graph.edgeId(v,w) == self.graph.edgeId(w,v) or self.graph.isDirected()
                        
                        if self.sstopk_skip_edge[self.graph.edgeId(v,w)]:
                            continue
                        if w==source or self.sstopk_skip_node[w]:
                            assert w not in succ
                            continue
                        if w not in pred:
                            forward_fringe.append(w)
                            pred[w] = v
                        if w in succ:
                            del forward_fringe
                            del reverse_fringe
                            return pred, succ, w
            else:
                this_level = reverse_fringe
                reverse_fringe = deque()
                for v in this_level:

                    
                    for w in self.othersideNeighbors(v):
                        
                        assert self.graph.edgeId(v,w) != self.graph.edgeId(w,v) or not self.graph.isDirected()
                        
                        if self.sstopk_skip_edge[self.graph.edgeId(w,v)]:
                            continue
                        
                        if w==target or self.sstopk_skip_node[w]:
                            assert w not in pred
                            continue
                        if w not in succ:
                            succ[w] = v
                            reverse_fringe.append(w)
                        if w in pred:
                            del forward_fringe
                            del reverse_fringe
                            return pred, succ, w
                        
        del forward_fringe
        del reverse_fringe
        
        raise NoPathException(f"No path between {source} and {target}.")
        
            


if __name__ == "__main__":
    

    parser = argparse.ArgumentParser()

    parser.add_argument('--g',metavar="GRAPH", required=True,  help='Path to the graph file (.hist or .nde format)')
    parser.add_argument('--k', metavar="K_VALUE", required=True, type=int, help='Number of top shortest paths to seek for', default=2)
    parser.add_argument('--r', metavar="NUM_ROOTS", required=False, type=int, help='Number of roots to consider (Default sqrt n)', default=-1)
    parser.add_argument('--ud', metavar="FORCE_UNDIRECTED", required=False, type=int, help='[0: unchanged 1: remove arc orientations]', default=-1)
    parser.add_argument('--uw', metavar="FORCE_UNWEIGHTED", required=False, type=int, help='[0: unchanged 1: remove arc weights]', default=-1)
    parser.add_argument('--s', metavar="(S)CC", required=False, type=int, help='[0: unchanged 1: extract largest (strongly) connected component]', default=-1)

    args = parser.parse_args()


    
    if ".hist" in str(args.g):
        G = read_hist(str(args.g))

    elif ".nde" in str(args.g):
        G = read_nde(str(args.g))

    else:
        raise Exception('unknown graph format')
        
    num_roots = int(args.r)
    
    

    
    G.removeMultiEdges()
    G.removeSelfLoops()
    
    G.indexEdges()
    print("init graph:",str(os.path.basename(args.g)),"directed:",G.isDirected(),"weighted:",G.isWeighted())
    print("vertices:",G.numberOfNodes(),"arcs:",G.numberOfEdges())

    remove_orientation = int(args.ud)
    
    
    if remove_orientation==1:
        new_G = None
        if G.isWeighted():
            new_G = nk.graph.Graph(directed=False,weighted=True)
            for u,v,w in G.iterEdgesWeights():
                new_G.addEdge(u,v,w,addMissing=True)
                
        else:
            new_G = nk.graph.Graph(directed=False,weighted=False)

            for u,v in G.iterEdges():
                new_G.addEdge(u,v,addMissing=True)
                
        new_G.indexEdges()
        del G
        G = new_G
        G.removeMultiEdges()
        G.removeSelfLoops()
        G.indexEdges()
        
        print("updated graph (removal of orientations):",str(os.path.basename(args.g)),"directed:",G.isDirected(),"weighted:",G.isWeighted())
        print("vertices:",G.numberOfNodes(),"arcs:",G.numberOfEdges())

   
    remove_weights = int(args.uw)
        
    if remove_weights==1:
        G = nk.graphtools.toUnweighted(G)
        G.indexEdges()
        print("updated graph (removal of weights):",str(os.path.basename(args.g)),"directed:",G.isDirected(),"weighted:",G.isWeighted())
        print("vertices:",G.numberOfNodes(),"arcs:",G.numberOfEdges())

   


    scc = int(args.s)
    
    if scc==1:  
        if not G.isDirected():
            cc = nk.components.ConnectedComponents(G)
            cc.run()
            G = cc.extractLargestConnectedComponent(G, True)
        else:
            cc = nk.components.StronglyConnectedComponents(G)
            cc.run()
            largest = None
            largest_size = 0
            if len(cc.getComponentSizes())>=1:
                for compon in cc.getComponents():
                    if len(compon)>largest_size:
                        largest = set(compon)
                        largest_size = len(compon)
                to_remove = []
                for ver in range(G.numberOfNodes()):
                    if ver in largest:
                        continue
                    to_remove.append(ver)
                assert len(set(to_remove))==len(to_remove)
                for r in to_remove:
                    G.removeNode(r)
                G = nk.graphtools.getCompactedGraph(G,nk.graphtools.getContinuousNodeIds(G))


        G.indexEdges()

        print("updated graph (scc):",str(os.path.basename(args.g)),"directed:",G.isDirected(),"weighted:",G.isWeighted())
        print("vertices:",G.numberOfNodes(),"arcs:",G.numberOfEdges())



    nk.overview(G)
        
    K = int(args.k)
    print(flush=True)   
    if K<1:
        K=2
        
    # aux_graph = nk.nxadapter.nk2nx(G)

    print("Value of K:",K,flush=True)   
    
    if not G.isDirected() or G.isWeighted():
        if G.numberOfNodes()>50000:
            print("DIAMETER ESTIMATION")
            diam = nk.distance.Diameter(G,algo=nk.distance.DiameterAlgo.ESTIMATED_SAMPLES,nSamples=100)
            diam.run()
        else:
            diam = nk.distance.Diameter(G,algo=nk.distance.DiameterAlgo.AUTOMATIC)
            diam.run()
        diametro = diam.getDiameter()[0]  
        del diam
        
    else:
        G_prime = nk.graphtools.toUndirected(G)
        print("DIAMETER ON UNDIRECTED DUE TO BUG")
        if G.numberOfNodes()>50000:
            print("DIAMETER ESTIMATION")
            diam = nk.distance.Diameter(G,algo=nk.distance.DiameterAlgo.ESTIMATED_SAMPLES,nSamples=100)
            diam.run()
        else:
            diam = nk.distance.Diameter(G_prime,algo=nk.distance.DiameterAlgo.AUTOMATIC)
            diam.run()
        diametro = diam.getDiameter()[0]  
        del diam
        del G_prime
    # if G.isWeighted():   
    #     diametro = nx.diameter(aux_graph, usebounds=True, weight='weight')
    # else:
    #     diametro = nx.diameter(aux_graph, usebounds=True, weight=None)
    
    # del aux_graph
    
    print("DIAMETER:",diametro,flush=True)   
    # print("\n",flush=True)
    # 

    now = datetime.now() # current date and time
    date_time = now.strftime("%d_%m_%Y_%H_%M_%S")

    statsfile = str(os.path.basename(args.g))+"_"+str(K)+"_sstopk_"+date_time+'.csv'
    

    cpu_yen  = []
    cpu_sstopk = []
    speedups = []
    pruned_visits = []
    extra_visits = []
    numero_non_saturi = [] 

    yen_calls = []

    randomly_selected_sqrt_roots = set()
    
  
    rootsfile = str(os.path.basename(args.g))+"_"+str(K)+"_roots.csv"
    
    
    if os.path.isfile(rootsfile):
        # Open file 
        with open(rootsfile) as csvfile: 
            reader_obj = csv.DictReader(csvfile,delimiter=";")
              
            # Iterate over each row in the csv file  
            # using reader object 
            for row in reader_obj: 
                
                
                cnt = 0
                splittaggio = row['roots'][1:-1].split(',')
                l = set()
                while cnt<len(splittaggio):
                    randomly_selected_sqrt_roots.add(int(row['roots'][1:-1].split(',')[cnt]))
                    cnt+=1
                break
                
    else:
        if num_roots == -1:
            
            num_roots = round(math.sqrt(G.numberOfNodes()))
            
            if G.numberOfNodes()>=20000:
                num_roots = 30
            if G.numberOfNodes()>=1000000:
                num_roots = 3
                
        if num_roots < 1:
            num_roots = 1
            
        if num_roots > G.numberOfNodes():
            num_roots = round(math.sqrt(G.numberOfNodes()))
            if G.numberOfNodes()>=30000:
                num_roots = 30                  
            if G.numberOfNodes()>=1000000:
                num_roots = 3
        
        while len(randomly_selected_sqrt_roots)<num_roots:
            randomly_selected_sqrt_roots.add(graphtools.randomNode(G))
            
        with open(rootsfile, 'w', newline='', encoding='UTF-8') as csvfile:
            writer = csv.writer(csvfile,delimiter=";")
            writer.writerow(["graph_name",\
                             "k",\
                             "roots"])
            writer.writerow([str(os.path.basename(args.g)),\
                             str(K),\
                             list(randomly_selected_sqrt_roots)])
                
    print("N_ROOTS:",len(randomly_selected_sqrt_roots))


    bar = PixelBar('Yen vs SSTOPK:', max = len(randomly_selected_sqrt_roots))
    

    if __debug__:
        aux_graph = nk.nxadapter.nk2nx(G)

    if __debug__ and G.numberOfNodes()<100:
        
        pos = nx.kamada_kawai_layout(aux_graph)    
        colori = ['#029386' for _ in range(aux_graph.number_of_nodes())]  #'#029386'
        fig, ax = plt.subplots(figsize=(10,10))
        nx.draw(aux_graph,pos, node_color=colori,node_size=800,font_size=14)
        nx.draw_networkx_labels(aux_graph,pos,font_family="sans-serif",font_size=14)
        ax.set_axis_off()
        fig.tight_layout()
        plt.show()
        
    randomly_selected_sqrt_roots = sorted(list(randomly_selected_sqrt_roots))    
    
    
    for first_root in randomly_selected_sqrt_roots:
        
        

        SSTK = single_source_top_k(G,K,first_root) 


        local_cpu_sstopk = time.perf_counter()
        SSTK.algo_sstopk()
        local_cpu_sstopk = time.perf_counter()-local_cpu_sstopk
        
        SSTK.deallocation()

        cpu_sstopk.append(local_cpu_sstopk)
        pruned_visits.append(SSTK.pruned_visits)
        extra_visits.append(SSTK.extra_visits)
        numero_non_saturi.append(SSTK.number_of_non_sat)
        yen_calls.append(SSTK.num_yen_calls)

        

        print(" done in:", round(local_cpu_sstopk,2), "seconds", flush=True)        
        
        nested_bar = IncrementalBar('Yen Iterations:', max = G.numberOfNodes())


        local_cpu_yen = 0
        
        YENTK = yens_algorithm(G,K)
        
        for second in range(G.numberOfNodes()):
            nested_bar.next()

            if first_root==second:
                continue
            
            cpu_yen_single_pair = time.perf_counter()
            
            top_k_yen = YENTK.run(first_root, second)

            local_cpu_yen += (time.perf_counter()-cpu_yen_single_pair)
            
            assert all(type(i)==tuple for i in top_k_yen)
            
            test_equality("BY",SSTK.top_k[second],top_k_yen)
            
            if __debug__:
                
                if nx.is_weighted(aux_graph):
                    try:
                        top_k_nx = list(islice(nx.shortest_simple_paths(aux_graph, first_root, second, weight='weight'), K))
                    except nx.NetworkXNoPath:
                        top_k_nx = []
                        pass
                else:
                    try:
                        top_k_nx = list(islice(nx.shortest_simple_paths(aux_graph, first_root, second, weight=None), K))    
                    except nx.NetworkXNoPath:
                        top_k_nx = []
                        pass
                    
                mypaths = []
                
                for outp in top_k_nx:
                    mypaths.append((sum([G.weight(u,v) for u, v in pairwise(outp)]),outp))
                    
                test_equality("YY",top_k_yen,mypaths)





            for i in top_k_yen:
                del i
            del top_k_yen
            
        cpu_yen.append(local_cpu_yen)        
        speedups.append(local_cpu_yen/local_cpu_sstopk)
        
        for i in SSTK.top_k:
            for j in i:
                del j
                
        del SSTK.top_k[:]
        nested_bar.finish()
 
        bar.next()

        print("\nTotal SSTopk CPUTime:", round(local_cpu_sstopk,2),"Total Yen CPUTime:", round(local_cpu_yen,2),"Speedup:",round(local_cpu_yen/local_cpu_sstopk,2), "Extra-visits:", SSTK.extra_visits,"of which pruned:", SSTK.pruned_visits, "Calls to Yen: ",SSTK.num_yen_calls, "Non saturi left: ",SSTK.number_of_non_sat,flush=True)

        del SSTK
        del YENTK
    if __debug__:
        del aux_graph




            

        

    bar.finish()

    assert len(cpu_yen)==len(cpu_sstopk)
    print("Total CPUTime Yen", round(sum(cpu_yen),2), "s")
    print("Total CPUTime SSTopk", round(sum(cpu_sstopk),2), "s")
    print("Avg CPUTime Yen", round(statistics.mean(cpu_yen),2), "s")
    print("Avg CPUTime SSTopk", round(statistics.mean(cpu_sstopk),2), "s")
    print("Avg Speedup", round(statistics.mean(speedups),2))
    print("Med Speedup", round(statistics.median(speedups),2))
    print("Avg Yen Calls", round(statistics.mean(yen_calls),2))


    assert len(cpu_sstopk)==len(cpu_yen)
    assert len(cpu_sstopk)==len(extra_visits)
    assert len(cpu_sstopk)==len(yen_calls)
    assert len(cpu_sstopk)==len(speedups)


    assert len(cpu_sstopk)==len(randomly_selected_sqrt_roots)

    with open(statsfile, 'a', newline='', encoding='UTF-8') as csvfile:
        
        writer = csv.writer(csvfile)
        
        finish_time = now.strftime("%d_%m_%Y_%H_%M_%S")


        writer.writerow(["graph_name",\
                         "date",\
                         "vertices",\
                         "arcs",\
                         "k",\
                         "diameter",\
                         "root",\
                         "yen_time",\
                         "sstopk_time",\
                         "speedup",\
                         "extra_visits",\
                         "pruned_visits",\
                         "yen_calls",
                         "num_non_sat"])
        
        for s in range(len(cpu_sstopk)):
            writer.writerow([str(args.g),\
                             str(finish_time),\
                             G.numberOfNodes(),\
                             G.numberOfEdges(),\
                             str(K),\
                             diametro,\
                             randomly_selected_sqrt_roots[s],\
                             round(cpu_yen[s],2),\
                             round(cpu_sstopk[s],2),\
                             round(speedups[s],2),\
                             round(extra_visits[s],0),\
                             round(pruned_visits[s],0),\
                             round(yen_calls[s],0),\
                             round(numero_non_saturi[s],0)])
            
        writer.writerow(["graph_name",\
                         "date",\
                         "vertices",\
                         "arcs",\
                         "k",\
                         "diameter",\
                         "n_roots",\
                         "tot_yen_time",\
                         "tot_sstopk_time",\
                         "avg_yen_time",\
                         "avg_sstopk_time",\
                         "med_yen_time",\
                         "med_sstopk_time",\
                         "avg_yen_calls",\
                         "avg_non_saturi",\
                         "avg_speedup",\
                         "med_speedup"])

        
        writer.writerow([str(args.g),\
                         str(finish_time),\
                         G.numberOfNodes(),\
                         G.numberOfEdges(),\
                         str(K),\
                         diametro,\
                         len(randomly_selected_sqrt_roots),\
                         round(sum(cpu_yen),2),\
                         round(sum(cpu_sstopk),2),\
                         round(statistics.mean(cpu_yen),2),\
                         round(statistics.mean(cpu_sstopk),2),\
                         round(statistics.median(cpu_yen),2),\
                         round(statistics.median(cpu_sstopk),2),\
                         round(statistics.mean(yen_calls),2),\
                         round(statistics.mean(numero_non_saturi),2),\
                         round(statistics.mean(speedups),2),\
                         round(statistics.median(speedups),2)])

            


