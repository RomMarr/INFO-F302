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


class Automate:
    def __init__(self, alphabet: str, pos: list[str], neg: list[str], k: int):
        # Variables
        self.etatPool = IDPool(start_from=1) 
        self.FPool = IDPool(start_from=100) 
        self.transiPool = IDPool(start_from=200) 
        self.execPool = IDPool(start_from=300) 
        self.cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)
        self.alphabet = alphabet
        self.pos = pos
        self.neg = neg
        self.k = k


    # Fonctions de création des clauses :
    def existance_etat_initial(self):
        # existance état initial :
        self.cnf.append([self.etatPool.id((0))])

    def transition_valide(self):
        for i in self.alphabet:
            for x in range(self.k):  # x = transition initiale
                for y in range(self.k):  # y  = transition finale
                    self.cnf.append([-self.transiPool.id((x,y,i)), self.etatPool.id((y))])
                    self.cnf.append([-self.transiPool.id((x,y,i)), self.etatPool.id((x))])

    def mot_commence_0(self):
        # Tout mot commence à 0 :
        for mot in (self.pos + self.neg):
            if mot != '' :
                self.cnf.append([self.execPool.id((0,0,mot))]) 

    def exec_finie_etat_non_acceptant(self):
        # Exécution finie sur état non-acceptant :
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for w in self.neg:
                    if w != '' :
                        lettre = w[-1]
                        self.cnf.append([-self.execPool.id((x,len(w)-1,w)),-self.transiPool.id((x,y,lettre)),-self.FPool.id((y))])

    def exec_finie_etat_acceptant(self):
        # Exécution finie sur état acceptant :
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for w in self.pos:
                    if w != '' :
                        lettre = w[-1]
                        self.cnf.append([-self.execPool.id((x,len(w)-1,w)),-self.transiPool.id((x,y,lettre)),self.FPool.id((y))])
                    
    def existe_1_chemin_mots_acceptants(self):
        # Il faut qu'il existe un chemin pour les mots acceptants :
        for mot in self.pos:
            for indiceLettre in range(len(mot)):
                d = []
                for x in range(self.k):
                    d.append(self.execPool.id((x, indiceLettre, mot)))
                self.cnf.append(d)                
                
    def un_chemin_possible(self):
        # # Un seul chemin possible :
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale 1 
                for z in range(self.k):  # y  = transition finale 2
                    if z != y:
                        for lettre in self.alphabet:
                            self.cnf.append([-self.transiPool.id((x,y,lettre)), -self.transiPool.id((x, z, lettre))])

    def lien_chemin_transition(self):
        # Lien entre chemin et transition :
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for mot in (self.pos + self.neg):
                    for indiceLettre in range(len(mot)):
                        lettre = mot[indiceLettre]
                        self.cnf.append([-self.execPool.id((x, indiceLettre, mot)), -self.execPool.id((y, indiceLettre+1, mot)), self.transiPool.id((x,y,lettre))])

    
    def chemin_implique_transition(self):
        # Chemin implique transition :
        for x in range(self.k):  # x = transition initiale
            for mot in (self.pos):
                for indiceLettre in range(len(mot)):
                    d=[]
                    d.append(-self.execPool.id((x, indiceLettre, mot)))
                    for y in range(self.k):
                        lettre = mot[indiceLettre]
                        d.append(self.transiPool.id((x,y,lettre)))
                    self.cnf.append(d)

    def transition_implique_chemin(self):
        # Transition implique chemin :
        for x in range(self.k):
            for y in range(self.k):
                for mot in (self.pos+self.neg):
                    for indiceLettre in range(len(mot)-1):
                        lettre = mot[indiceLettre]
                        self.cnf.append([-self.transiPool.id((x,y,lettre)), -self.execPool.id((x,indiceLettre,mot)), self.execPool.id((y,indiceLettre+1,mot))])


    # Fonction de création d'un DFA à partir des clauses : 
    def create_dfa(self) -> DFA:
        s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
        # s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
        s.append_formula(self.cnf.clauses, no_return=False)

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
        if not resultat:
            return None
        for soluce in interpretation_filtree :
            if soluce < 100:
                states.add('q'+str(soluce-1))
            elif soluce < 200:
                accepting.add('q'+str(soluce-100))
            elif soluce < 300 :
                if 'q'+str((soluce-200)//self.k) not in transitions:  
                    temp =  dict()
                    temp[self.alphabet[(soluce-200)//self.k**2]] = 'q'+str((soluce-200)%self.k)
                    transitions['q'+str((soluce-200)//self.k)] = temp
                else :
                    temp_dict = transitions['q'+str((soluce-200)//self.k)]
                    temp_dict[self.alphabet[(soluce-200)//self.k**2]] = temp_dict.setdefault(self.alphabet[(soluce-200)//self.k**2], set()).add('q'+str((soluce-200)%self.k))
        print (states)
        print(transitions)
        print(accepting)
        return DFA(states=states, input_symbols=set(self.alphabet), transitions=transitions, initial_state="q0", final_states=accepting)





"""def etat_acceptant_ou_non(k: int):
    # Chaque état est acceptant ou non :
    for x in range(k):
        cnf.append([FPool.id((x)),-FPool.id((x))])"""






# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  # existance état initial
    a.transition_valide()  # Transition valide  
    a.mot_commence_0()  # Tout mot commence à 0
    a.lien_chemin_transition()  # Lien entre chemin et transition
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()  # Transition implique chemin
    a.un_chemin_possible()  # Un seul chemin possible
    a.existe_1_chemin_mots_acceptants()  # Il faut qu'il existe un chemin pour les mots acceptants
    a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant

    #print(cnf.clauses)
    #show_automaton(create_dfa(alphabet, k))
    return a.create_dfa()
    

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