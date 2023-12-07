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
    cnf.append([etatPool.id((0))])

    # Transition valide : 
    for i in alphabet:
        for x in range(k):  # x = transition initiale
            for y in range(k):  # y  = transition finale
                cnf.append([-transiPool.id((x,y,i)), etatPool.id((y))]) 

    # Tout mot commence à 0 :
    for mot in (pos + neg):
        if mot != '' :
            cnf.append([execPool.id((0,mot[0],mot))]) 

    # # Lien entre chemin et transition :
    # for x in range(k):  # x = transition initiale
    #     for y in range(k):  # y  = transition finale
    #         for mot in (pos + neg):
    #             for indiceLettre in range(len(mot)):
    #                 cnf.append([-execPool.id((x, indiceLettre, mot)), -execPool.id((y, indiceLettre+1, mot)), -transiPool.id((x,y,mot[indiceLettre]))])

    # # # Un seul chemin possible :
    # for x in range(k):  # x = transition initiale
    #     for y in range(k):  # y  = transition finale 1 
    #         for z in range(k):  # y  = transition finale 2
    #             if z != y:
    #                 for lettre in alphabet:
    #                     cnf.append([-transiPool.id((x,y,lettre)), -transiPool.id((x, z, lettre))])

    # # Exécution finie sur état acceptant :
    # for x in range(k):  # x = transition initiale
    #     for y in range(k):  # y  = transition finale
    #         for w in pos:
    #             if w != '' :
    #                 cnf.append([-execPool.id((x,w[-1],w)),-transiPool.id((x,y,w[-1])),FPool.id((y))])

    # # Exécution finie sur état non-acceptant :
    # for x in range(k):  # x = transition initiale
    #     for y in range(k):  # y  = transition finale
    #         for w in neg:
    #             if w != '' :
    #                 cnf.append([-execPool.id((x,w[-1],w)),-transiPool.id((x,y,w[-1])),-FPool.id((y))])
    
    print(cnf.clauses)
    
    
    s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
    # s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
    s.append_formula(cnf.clauses, no_return=False)

    print("Resolution...")
    resultat = s.solve()
    print("Satisfaisable : " + str(resultat))
    print("Temps de resolution : " + '{0:.2f}s'.format(s.time()))
    interpretation = s.get_model()
    print(interpretation)




    
        

                    
                


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
    #main()
    gen_aut('a',['a'],['aa'], 2)


POSITIVE_DFA_INSTANCES = [
    # L(A) = words of even length
    ('a',  ['', 'aa', 'aaaaaa'], ['a', 'aaa', 'aaaaa'], 2),
    # L(A) = a^*
    ('ab', ['', 'a', 'aa', 'aaa', 'aaaa'], ['b', 'ab', 'ba', 'bab', 'aba'], 1),
    # L(A) = words with at least one b
    ('ab', ['b', 'ab', 'ba', 'abbb', 'abba'], ['', 'aaa', 'a', 'aa'], 2),
    # L(A) = words where every chain consecutive b's has length >= 2
    ('ab', ['', 'aa', 'aaaa', 'a', 'abb', 'bb', 'abba', 'bbbb', 'bbba', 'abbb'],
           ['b', 'aba', 'ba', 'ab', 'abbab', 'bbabbab', 'babba'], 3),
    # L(A) = {aa, ab, ba}
    ('ab', ['aa', 'ab', 'ba'], ['', 'a', 'b', 'bb', 'aaa', 'aba', 'bba'], 4),
    # L(A) = a^+ @ a^+ . a^+
    ('a@.', ['a@a.a', 'aa@a.a'],
            ['', '.', '..a', '.a', '@', '@.', '@.a', '@a', '@a.', '@a.a', '@aa', 'a', 'a.', 'a.a', 'a@',
            'a@.', 'a@.a', 'a@a', 'a@a.', 'a@aa', 'aa', 'aa.', 'aa.a', 'aaa'], 6),
]