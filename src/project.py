from utils import *
from tests import *

from automata.fa.fa import FA
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA

from pysat.solvers import Minisat22, Minicard
from pysat.formula import CNF, CNFPlus, IDPool

X(i[0,k],a[0,1] -> a=1 appartient à F,l[lettre aplhabet],j[0,k])

# Variables 
vpool = IDPool(start_from=1) 
cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)


# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # pos : P (ensemble des mots acceptant)
    # neg : N (ensemble des mots non-acceptant)
    
    
    # Un etat ne peux pas être acceptant et non acceptant en même temps
    for etatI in range(k):
        for lettre in alphabet:
            for  etatF in range(k):
                    cnf.append([-vpool.id(etatI,0,lettre,etatF), -vpool.id(etatI,1,lettre,etatF)])
    
    # Commence à P0
    
    for a in range(2) :
        for mot in pos:
            for etatF in range(k) :
                cnf.append([vpool.id(0,a,mot[0],etatF)])

    # Pas deux transitions possible
        for etatI in range(k) :
            for lettre in alphabet :
                for a in range(2) :
                    for etatF1 in range(k) :
                        for etatF2 in range(k) :
                            cnf.append(-[vpool.id(etatI,a,lettre,etatF1),-vpool.id(etatI,a,lettre,etatF2)])

    # Tout mots de pos finit par un etat acceptant
        for mot in pos :
            for lettre in range(len(mot)-2):
                for etatI1 in range(k) :
                    for etatF in range(k) :
                        for a in range(2) :
                            for etatI2 in range(k) :
                                cnf.append(-[vpool.id(etatI1,a,mot[lettre+1],etatF)], - [vpool.id(etatI2,a,mot[lettre],etatI)])

                    
                


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
