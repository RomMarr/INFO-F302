"""
Cours : INFO-F302, Informatique fondamentale
Projet : Apprentissage automatique de programmes de validation de chaînes de caractères
Membres : Noé Vekemans (000475625), Romain Markowitch (000540172) et Camille Leduc (000517774)
Date : 15 décembre 2023
"""


# Imports
from utils import *
from tests import *

from automata.fa.fa import FA
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA

from pysat.solvers import Minisat22, Minicard
from pysat.formula import CNF, CNFPlus, IDPool


# Variables
etatPool = IDPool(start_from=1) 
FPool = IDPool(start_from=100) 
transiPool = IDPool(start_from=200) 
execPool = IDPool(start_from=300) 


cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)

# Fonctions de création des clauses :
def existance_etat_initial():
    # existance état initial :
    cnf.append([etatPool.id((0))])


"""def etat_acceptant_ou_non(k: int):
    # Chaque état est acceptant ou non :
    for x in range(k):
        cnf.append([FPool.id((x)),-FPool.id((x))])"""

def transition_valide(alphabet: str, k: int):
    for i in alphabet:
        for x in range(k):  # x = transition initiale
            for y in range(k):  # y  = transition finale
                cnf.append([-transiPool.id((x,y,i)), etatPool.id((y))])
                cnf.append([-transiPool.id((x,y,i)), etatPool.id((x))])

def mot_commence_0(pos: list[str], neg: list[str]):
    # Tout mot commence à 0 :
    for mot in (pos + neg):
        if mot != '' :
            cnf.append([execPool.id((0,0,mot))]) 

def exec_finie_etat_non_acceptant(neg: list[str], k: int):
    # Exécution finie sur état non-acceptant :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale
            for w in neg:
                if w != '' :
                    lettre = w[-1]
                    cnf.append([-execPool.id((x,len(w)-1,w)),-transiPool.id((x,y,lettre)),-FPool.id((y))])

def exec_finie_etat_acceptant(pos: list[str], k: int):
    # Exécution finie sur état acceptant :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale
            for w in pos:
                if w != '' :
                    lettre = w[-1]
                    cnf.append([-execPool.id((x,len(w)-1,w)),-transiPool.id((x,y,lettre)),FPool.id((y))])
                
def existe_1_chemin_mots_acceptants(pos: list[str], k: int):
    # Il faut qu'il existe un chemin pour les mots acceptants :
    for mot in pos:
        for indiceLettre in range(len(mot)):
            d = []
            for x in range(k):
                d.append(execPool.id((x, indiceLettre, mot)))
            cnf.append(d)                
                
def un_chemin_possible(alphabet: str, k: int):
    # # Un seul chemin possible :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale 1 
            for z in range(k):  # y  = transition finale 2
                if z != y:
                    for lettre in alphabet:
                        cnf.append([-transiPool.id((x,y,lettre)), -transiPool.id((x, z, lettre))])

def lien_chemin_transition(pos: list[str], neg: list[str], k: int):
    # Lien entre chemin et transition :
    for x in range(k):  # x = transition initiale
        for y in range(k):  # y  = transition finale
            for mot in (pos + neg):
                for indiceLettre in range(len(mot)):
                    lettre = mot[indiceLettre]
                    cnf.append([-execPool.id((x, indiceLettre, mot)), -execPool.id((y, indiceLettre+1, mot)), transiPool.id((x,y,lettre))])

    
def chemin_implique_transition(pos: list[str], neg: list[str], k: int):
    # Chemin implique transition :
    for x in range(k):  # x = transition initiale
        for mot in (pos):
            for indiceLettre in range(len(mot)):
                d=[]
                d.append(-execPool.id((x, indiceLettre, mot)))
                for y in range(k):
                    lettre = mot[indiceLettre]
                    d.append(transiPool.id((x,y,lettre)))
                cnf.append(d)

def transition_implique_chemin(pos: list[str], neg: list[str], k: int):
    # Transition implique chemin :
    for x in range(k):
        for y in range(k):
            for mot in (pos+neg):
                for indiceLettre in range(len(mot)-1):
                    lettre = mot[indiceLettre]
                    cnf.append([-transiPool.id((x,y,lettre)), -execPool.id((x,indiceLettre,mot)), execPool.id((y,indiceLettre+1,mot))])


# Fonction de création d'un DFA à partir des clauses : 
def create_dfa(alphabet: str, k: int) -> DFA:
    
    s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
    # s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
    s.append_formula(cnf.clauses, no_return=False)

    #print("Resolution...")
    resultat = s.solve()
    #print("Satisfaisable : " + str(resultat))
    #print("Temps de resolution : " + '{0:.2f}s'.format(s.time()))
    interpretation = s.get_model()
    if resultat :
        interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
        #print(interpretation_filtree)
    
    states = set()
    transitions = dict()
    accepting = set()
    
    for soluce in interpretation_filtree :
        if soluce < 100:
            states.add('q'+str(soluce-1))
        elif soluce < 200:
            accepting.add('q'+str(soluce-100))
        elif soluce < 300 :
            if 'q'+str((soluce-200)//k) not in transitions:  
                temp =  dict()
                temp[alphabet[(soluce-200)//k**2]] = 'q'+str((soluce-200)%k)
                transitions['q'+str((soluce-200)//k)] = temp
            else :
                temp_dict = transitions['q'+str((soluce-200)//k)]
                temp_dict[alphabet[(soluce-200)//k**2]] = temp_dict.setdefault(alphabet[(soluce-200)//k**2], set()).add('q'+str((soluce-200)%k))
    print (states)
    print(transitions)
    print(accepting)
    return DFA(states=states, input_symbols=set(alphabet), transitions=transitions, initial_state="q0", final_states=accepting)





# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    existance_etat_initial()  # existance état initial
    transition_valide(alphabet, k)  # Transition valide  
    mot_commence_0(pos, neg)  # Tout mot commence à 0
    lien_chemin_transition(pos, neg, k)  # Lien entre chemin et transition
    chemin_implique_transition(pos, neg, k)   # Chemin implique transition
    transition_implique_chemin(pos, neg, k)  # Transition implique chemin
    un_chemin_possible(alphabet, k)  # Un seul chemin possible
    existe_1_chemin_mots_acceptants(pos, k)  # Il faut qu'il existe un chemin pour les mots acceptants
    exec_finie_etat_acceptant(pos, k)  # Exécution finie sur état acceptant
    exec_finie_etat_non_acceptant(neg, k)  # Exécution finie sur état non-acceptant

    #print(cnf.clauses)
    #show_automaton(create_dfa(alphabet, k))
    return create_dfa(alphabet, k)
    

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
    #test_minaut()
    #test_autc()
    #test_autr()
    #test_autcard()
    #test_autn()

if __name__ == '__main__':
    main()
        # cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)
        # print(elem)
        # gen_aut(elem[0],elem[1],elem[2],elem[3])


POSITIVE_DFA_INSTANCES = [
    # L(A) = words of even length Y
    ('a',  ['', 'aa', 'aaaaaa'], ['a', 'aaa', 'aaaaa'], 2),
    # L(A) = a^* :(
    ('ab', ['', 'a', 'aa', 'aaa', 'aaaa'], ['b', 'ab', 'ba', 'bab', 'aba'], 1),
    # L(A) = words with at least one b Y
    ('ab', ['b', 'ab', 'ba', 'abbb', 'abba'], ['', 'aaa', 'a', 'aa'], 2),
    # L(A) = words where every chain consecutive b's has length >= 2 Y
    ('ab', ['', 'aa', 'aaaa', 'a', 'abb', 'bb', 'abba', 'bbbb', 'bbba', 'abbb'],
           ['b', 'aba', 'ba', 'ab', 'abbab', 'bbabbab', 'babba'], 3),
    # L(A) = {aa, ab, ba}
    ('ab', ['aa', 'ab', 'ba'], ['', 'a', 'b', 'bb', 'aaa', 'aba', 'bba'], 4),
    # L(A) = a^+ @ a^+ . a^+
    ('a@.', ['a@a.a', 'aa@a.a'],
            ['', '.', '..a', '.a', '@', '@.', '@.a', '@a', '@a.', '@a.a', '@aa', 'a', 'a.', 'a.a', 'a@',
            'a@.', 'a@.a', 'a@a', 'a@a.', 'a@aa', 'aa', 'aa.', 'aa.a', 'aaa'], 6),
]