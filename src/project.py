from utils import *
from tests import *

from automata.fa.fa import FA
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA

from pysat.solvers import Minisat22, Minicard
from pysat.formula import CNF, CNFPlus, IDPool

X(i[0,k],a[0,1] -> a=1 appartient à F,w [mots de pos union neg], lettres [alphabet])

# Variables 
vpool = IDPool(start_from=1) 
cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)


# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # pos : P (ensemble des mots acceptant)
    # neg : N (ensemble des mots non-acceptant)
    
    
    # Un etat ne peux pas être acceptant et non acceptant en même temps
    for etatI in range(k):
        for lettre1 in alphabet:
            for mot1 in (pos + neg):
                for lettre2 in alphabet:
                    for mot2 in (pos+neg):
                        cnf.append([-vpool.id(etatI,0, mot1,lettre1), -vpool.id(etatI, 1, mot2, lettre2)])
    
    # Commence à P0
    
    for a in range(2) :
        for mot in pos:
                cnf.append([vpool.id(0, a, mot, mot[0])])

    # Un mot ne peux pas être sur deux états différents à la même lettres
    for etat1 in range(k) :
        for etat2 in range(k):
            for mot in (pos+neg) :
                for a in range(2) :
                    for i in range(len(mot)):
                        cnf.append(-[vpool.id(etat1,a,mot, mot[i]),-vpool.id(etat2,a,mot,mot[i])])

    # Tout mots de pos finissent par un etat acceptant
    for mot in pos :
        d=[]
        for etatI in range(k) :
            d.append([vpool.id(etatI, 1 ,mot, mot[-1])])
        cnf.append(d)

    # Tout mots de neg finissent par un etat non-acceptant 'ou ne finisse pas'
    for mot in neg :
        d = []
        for etatI in range(k) :
            d.append([vpool.id(etatI, 0 ,mot, mot[-1])])
        cnf.append(d)
        
    # La clause chaude

    
        

                    
                


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
