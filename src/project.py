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
    def __init__(self, alphabet: str, pos: list[str], neg: list[str], k: int, ell = -1):
        # Variables
        self.etatPool = IDPool(start_from=1) 
        self.FPool = IDPool(start_from=k+1) 
        self.transiPool = IDPool(start_from=2*k+1) 
        self.execPool = IDPool(start_from=2*k+(k**2)*len(alphabet)+1) 
        
        if ell == -1 :
            self.cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)
        else:
            self.cnf = CNFPlus()
        self.alphabet = alphabet
        self.pos = pos
        self.neg = neg
        self.k = k
        self.ell = ell
        self.interpretation_filtree = None

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
            self.cnf.append([self.execPool.id((0,0,mot))]) 

    def exec_finie_etat_non_acceptant(self):
        # Exécution finie sur état non-acceptant :
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for w in self.neg:
                    if w != '' :
                        lettre = w[-1]
                        self.cnf.append([-self.execPool.id((x,len(w)-1,w)),-self.transiPool.id((x,y,lettre)),-self.FPool.id((y))])
                    else :
                        self.cnf.append([-self.FPool.id((0))])

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
        for mot in (self.pos):
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
                for mot in (self.pos+self.neg):
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

    def au_moins_une_transi(self):
        d = []
        for x in range(self.k):
            for y in range(self.k):
                for lettre in self.alphabet:
                    d.append(self.transiPool.id((x,y,lettre)))
        self.cnf.append(d)
    
    def automate_complet(self):
        for x in range(self.k):
            for lettre in (self.alphabet) :
                d=[]
                for y in range(self.k) :
                    d.append(self.transiPool.id((x,y,lettre)))
                self.cnf.append(d)

    def automate_reversible(self):
        for y in range(self.k):  # sommet d'arrivé
            for lettre in (self.alphabet):
                for x1 in range(self.k) :  # sommet de départ 1
                    for x2 in range(self.k) :  # sommet de départ 2
                        if x1 != x2 :
                            self.cnf.append([-self.transiPool.id((x1,y,lettre)), -self.transiPool.id((x2,y,lettre))])

    def au_plus_ell_etats_acceptant(self):
        d = []
        for x in range(self.k) : # sommet           
            d.append(self.FPool.id((x)))
        atmost = [d,self.ell]
        self.cnf.append(atmost, is_atmost=True)

    
    def etat_final(self):
        for mot in self.pos:
            for x in range(self.k):
                for y in range(self.k):
                    lettre = mot[-1]
                    self.cnf.append(-self.execPool.id((x,len(mot)-1,mot)),-self.transiPool.id((x,y,lettre)),self.etatFinal.id((y,mot)))   

    def solve_aut(self):
        s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
        #s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
        s.append_formula(self.cnf.clauses, no_return=False)
        # s.append_formula(self.cnf.atmosts, no_return= False)
        resultat = s.solve()
        interpretation = s.get_model()
        if resultat :
            self.interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
        self.interpretation_filtree
        return resultat
    
    def solve_autcard(self) :
        s = Minicard(use_timer=True)  # pour utiliser le solveur Minicard (seulement pour la question 6)
        s.append_formula(self.cnf.clauses, no_return=False)
        s.append_formula(self.cnf.atmosts, no_return= False)
        resultat = s.solve()
        interpretation = s.get_model()
        if resultat :
            self.interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
        self.interpretation_filtree
        return resultat
    


    # Fonction de création d'automates (DFA et NFA) à partir des clauses : 
    def create_dfa(self, resultat) -> DFA:
        states = set()
        transitions = dict()
        accepting = set()
        if not resultat:
            return None
        bornEtat = self.k+1
        bornF = 2*self.k+1
        bornTransi = 2*self.k+(self.k**2)*len(self.alphabet)+1
        for soluce in self.interpretation_filtree :
            if soluce < bornEtat:
                states.add('q'+str(soluce-1))
            elif soluce < bornF:
                accepting.add('q'+str(soluce-self.k-1))
            elif soluce < bornTransi :
                sommetDepart = 'q'+str(((soluce-2*self.k-1)//self.k)%self.k)
                lettre = self.alphabet[(soluce-2*self.k-1)//self.k**2]
                sommetArive = 'q'+str((soluce-2*self.k-1)%self.k)
                if sommetDepart not in transitions:  
                    temp =  dict()
                    temp[lettre] = sommetArive
                else :
                    temp = transitions[sommetDepart]
                    temp[lettre] = sommetArive
                transitions[sommetDepart] = temp
        for sommet in states :
            if sommet not in transitions:
                transitions[sommet] = dict()
        print (states)
        print(transitions)
        print(accepting)
        return DFA(states=states, input_symbols=set(self.alphabet), transitions =transitions, initial_state ="q0", final_states = accepting, allow_partial=True)
    
class AutomateNFA(Automate):
    def __init__(self, alphabet: str, pos: list[str], neg: list[str], k: int, ell = -1):
        somme = 0
        for mot in pos:
            somme += len(mot)*k
        self.finalPool = IDPool(start_from= 1000)
        super().__init__(alphabet,pos,neg,k,ell)
        self.cnf = CNFPlus()
    
    def lien_etat_final_transition(self) :
        for x in range(self.k):
            for y in range(self.k):
                for mot in self.pos:
                    if mot != '':
                        lettre = mot[-1]    # Dernière lettre du mot
                        i = len(mot)-1  # Indice de la dernière lettre du mot
                        self.cnf.append([-self.execPool.id((x,i,mot)),-self.transiPool.id((x,y,lettre)),-self.FPool.id((y)), self.finalPool.id((x,y,mot))])
                        self.cnf.append([-self.finalPool.id((x,y,mot)),self.transiPool.id((x,y,lettre))])
                        self.cnf.append([-self.finalPool.id((x,y,mot)),self.execPool.id((x,i,mot))])
                    else:
                        self.cnf.append([self.FPool.id((0))])
                

    def etat_final_implique_etat_acceptant (self) :
        for x in range(self.k):
            for mot in self.pos:
                for y in range(self.k):
                    self.cnf.append([-self.finalPool.id((x,y,mot)),self.FPool.id((y))])

    
    def au_moins_un_etat_acceptant(self):
        for mot in self.pos:
            if mot!='':
                d = []
                for x in range(self.k) : # sommet  
                    for y in range(self.k) :         
                        d.append(self.finalPool.id((x,y,mot)))
                self.cnf.append(d)

    
    def create_nfa(self, resultat):
        states = set()
        transitions = dict()
        accepting = set()
        print(self.interpretation_filtree)
        if not resultat:
            return None
        bornEtat = self.k+1
        bornF = 2*self.k+1
        bornTransi = 2*self.k+(self.k**2)*len(self.alphabet)+1
        for soluce in self.interpretation_filtree :
            if soluce < bornEtat:
                states.add('q'+str(soluce-1))
            elif soluce < bornF:
                accepting.add('q'+str(soluce-self.k-1))
            elif soluce < bornTransi :
                sommetDepart = 'q'+str(((soluce-2*self.k-1)//self.k)%self.k)
                lettre = self.alphabet[(soluce-2*self.k-1)//self.k**2]
                sommetArive = 'q'+str((soluce-2*self.k-1)%self.k)
                if sommetDepart not in transitions:  
                    temp =  dict()
                    temp[lettre] = {sommetArive}
                else :
                    temp = transitions[sommetDepart]
                    temp[lettre] = temp.get(lettre,set())
                    temp[lettre].add(sommetArive)
                transitions[sommetDepart] = temp
        print(states)
        print(transitions)
        print(accepting)
        return NFA(states=states, input_symbols=set(self.alphabet), transitions =transitions, initial_state ="q0", final_states =accepting)

# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  # existance état initial
    a.transition_valide()  # Transition valide  
    a.mot_commence_0()  # Tout mot commence à 0
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()  # Transition implique chemin
    a.un_chemin_possible()  # Un seul chemin possible
    a.existe_1_chemin_mots_acceptants()  # Il faut qu'il existe un chemin pour les mots acceptants
    a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    resultat = a.solve_aut()
    return a.create_dfa(resultat)
    
# Q3
def gen_minaut(alphabet: str, pos: list[str], neg: list[str]) -> DFA:
    k = 1
    resultat = False
    
    while not resultat :
        a = Automate(alphabet, pos, neg, k)
        a.existance_etat_initial()  # existance état initial
        a.transition_valide()  # Transition valide  
        a.mot_commence_0()  # Tout mot commence à 0
        a.chemin_implique_transition()   # Chemin implique transition
        a.transition_implique_chemin()  # Transition implique chemin
        a.un_chemin_possible()  # Un seul chemin possible
        a.existe_1_chemin_mots_acceptants()  # Il faut qu'il existe un chemin pour les mots acceptants
        a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
        a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
        a.au_moins_une_transi() # Pour ne pas avoir d'erreur lors de la création de l'automate
        resultat = a.solve_aut()
        k+=1
    return a.create_dfa(resultat)

# Q4
def gen_autc(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  # existance état initial
    a.transition_valide()  # Transition valide  
    a.mot_commence_0()  # Tout mot commence à 0
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()  # Transition implique chemin
    a.un_chemin_possible()  # Un seul chemin possible
    a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    a.automate_complet()
    resultat = a.solve_aut()
    return a.create_dfa(resultat)

# Q5
def gen_autr(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  # existance état initial
    a.transition_valide()  # Transition valide  
    a.mot_commence_0()  # Tout mot commence à 0
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()  # Transition implique chemin
    a.un_chemin_possible()  # Un seul chemin possible
    a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    a.automate_reversible()
    resultat = a.solve_aut() 
    return a.create_dfa(resultat)

# Q6
def gen_autcard(alphabet: str, pos: list[str], neg: list[str], k: int, ell: int) -> DFA:
    a = Automate(alphabet, pos, neg, k, ell)
    a.existance_etat_initial()  # existance état initial
    a.transition_valide()  # Transition valide  
    a.mot_commence_0()  # Tout mot commence à 0
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()  # Transition implique chemin
    a.un_chemin_possible()  # Un seul chemin possible
    a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    a.au_plus_ell_etats_acceptant()
    resultat = a.solve_autcard() 
    return a.create_dfa(resultat)

# Q7
def gen_autn(alphabet: str, pos: list[str], neg: list[str], k: int) -> NFA:
    a = AutomateNFA(alphabet, pos, neg, k)
    a.existance_etat_initial()  # existance état initial
    a.mot_commence_0()  # Tout mot commence à 0
    a.transition_valide()
    a.existe_1_chemin_mots_acceptants()
    a.transition_implique_chemin()  # Transition implique chemin
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    a.lien_etat_final_transition()
    a.etat_final_implique_etat_acceptant()
    a.au_moins_un_etat_acceptant()
    a.lien_chemin_transition()
    resultat = a.solve_aut() 
    return a.create_nfa(resultat)

def main():
    test_aut()
    test_minaut()
    test_autc()
    test_autr()
    test_autcard()
    test_autn()

if __name__ == '__main__':
    main()

