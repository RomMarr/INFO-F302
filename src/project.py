from utils import *
from tests import *

from automata.fa.fa import FA
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA

from pysat.solvers import Minisat22, Minicard
from pysat.formula import CNF, CNFPlus, IDPool

# Variables 
etatPool = IDPool(start_from=1) 
FPool = IDPool(start_from=1) 
transiPool = IDPool(start_from=1) 
execPool = IDPool(start_from=1) 


cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)


# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # pos : P (ensemble des mots acceptant)
    # neg : N (ensemble des mots non-acceptant)
    
    # existance état initial :
    cnf.append([etatPool.id(0)])

    # Transition valide : 
    for i in alphabet:
        for x in range(k):  # x = transition initiale
            for y in range(k):  # y  = transition finale
                cnf.append([-transiPool.id(x,y,i), etatPool.id(y)]) 

    # Tout mot commence à 0 :
    for mot in (pos + neg):
        cnf.append([execPool.id(0,mot[0],mot)]) 

    # Lien entre chemin et transition :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale
            for mot in (pos + neg):
                for lettre in len(mot):
                    cnf.append([-execPool.id(x, lettre, mot), -execPool.id(y, lettre+1, mot), -transiPool.id(x,y,mot[lettre])])

    # Un seul chemin possible :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale 1 
            for z in range(k):  # y  = transition finale 2
                if z != y:
                    for lettre in alphabet:
                        cnf.append([-transiPool(x,y,lettre), -transiPool(x, z, lettre)])

    # Exécution finie sur état acceptant :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale
            for w in pos:
                cnf.append([-execPool()])






    
        

                    
                


    return "Oui"

# Q3
def gen_minaut(alphabet: str, pos: list[str], neg: list[str]) -> DFA:
    # À COMPLÉTER
    pass

# Q4
def gen_autc(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # À COMPLÉTER
    pass

# Q5
def gen_autr(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # À COMPLÉTER
    pass

# Q6
def gen_autcard(alphabet: str, pos: list[str], neg: list[str], k: int, ell: int) -> DFA:
    # À COMPLÉTER
    pass

# Q7
def gen_autn(alphabet: str, pos: list[str], neg: list[str], k: int) -> NFA:
    # À COMPLÉTER
    pass

def main():
    test_aut()
    test_minaut()
    test_autc()
    test_autr()
    test_autcard()
    test_autn()

if __name__ == '__main__':
    main()
