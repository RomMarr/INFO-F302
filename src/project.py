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
        self.qPool = IDPool(start_from=1)      # Variable pour les états de l'automate 
        self.fPool = IDPool(start_from=k+1)    # Variable pour les états acceptant de l'automate
        self.dPool = IDPool(start_from=2*k+1)  # Variable des transitions de l'automate
        self.ePool = IDPool(start_from=2*k+(k**2)*len(alphabet)+1)   # Variable pour l'execution des mots
        
        if ell == -1 :
            self.cnf = CNF()  # Construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)
        else:
            self.cnf = CNFPlus()    # Même chose mais pour CNFPlus permet des contraintes de cardinalité
        
        self.alphabet = alphabet  # Alphabet de l'automate
        self.pos = pos  # Les mots devant posséder une execution acceptante
        self.neg = neg  # Les mots ne devant pas posséder d'execution acceptante
        self.k = k      # Le nombre maximal de état de l'automate
        self.ell = ell  # Le nombre maximal d'état accéptant de l'automate (question 6)
        self.interpretation_filtree = None  

    # Fonctions de création des clauses :
    def existance_etat_initial(self):
        """ Existance de l'état initial """ 
        self.cnf.append([self.qPool.id((0))])

    def transition_valide(self):
        """ Chaque transition doit partir et arriver à un sommet valide """
        for i in self.alphabet:
            for x in range(self.k):  # x = état initial
                for y in range(self.k):  # y  = état final 
                    self.cnf.append([-self.dPool.id((x,y,i)), self.qPool.id((y))])  # Existance état final
                    self.cnf.append([-self.dPool.id((x,y,i)), self.qPool.id((x))])  # Existance état initial

    def mot_commence_0(self):
        """ Tout mot commence à 0 """
        for mot in (self.pos + self.neg):
            if mot != "":
                d=[]
                for y in range(self.k):
                    d.append(self.ePool.id((0,y,0,mot)))
                self.cnf.append(d)

    def exec_finie_etat_non_acceptant(self):
        """ Les exécutions des mots de neg finissent sur des états non-acceptants """
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for m in self.neg:  # m = mot de neg
                    if m != "" :
                        self.cnf.append([-self.ePool.id((x,y,len(m)-1,m)),-self.fPool.id((y))])
                    else :
                        self.cnf.append([-self.fPool.id((0))])  # Si le mot vide appartient à neg alors l'état
                                                                # q0 doit être non-acceptant
                        

    def exec_finie_etat_acceptant(self):
        """ Les exécutions des mots de pos finissent sur des états acceptants """
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for m in self.pos:  # m = mot de neg
                    if m != '' :
                        self.cnf.append([-self.ePool.id((x,y,len(m)-1,m)),self.fPool.id((y))])
                    else:
                        self.cnf.append([self.fPool.id((0))])

                    
    def existe_un_chemin_mots_acceptants(self):
        """ Il faut qu'il existe un chemin pour tout les mots de pos """
        for mot in (self.pos):
            for indiceLettre in range(len(mot)):
                d = []
                for x in range(self.k):
                    for y in range(self.k):
                        d.append(self.ePool.id((x,y, indiceLettre, mot)))
                self.cnf.append(d)    
            
                
    def une_seule_transition_possible(self):
        """ Pas deux transitions possible à partir du même état avec la même lettre """ 
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale 1 
                for z in range(self.k):  # z  = transition finale 2
                    if z != y:
                        for lettre in self.alphabet:
                            self.cnf.append([-self.dPool.id((x,y,lettre)), -self.dPool.id((x, z, lettre))])

    
    def chemin_implique_transition(self):
        """ Chemin implique transition : """
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):
                for mot in (self.pos):
                    for indiceLettre in range(len(mot)):
                        self.cnf.append([-self.ePool.id((x,y,indiceLettre,mot)), self.dPool.id((x,y,mot[indiceLettre]))])

    def transition_implique_chemin(self):
        """ Transition implique chemin : """
        for x in range(self.k):
            for y in range(self.k):
                for z in range(self.k):
                    for mot in (self.pos+self.neg):
                        for indiceLettre in range(len(mot)-1):
                            lettre = mot[indiceLettre+1]    # Lettre suivante du mot
                            self.cnf.append([ -self.ePool.id((x,y,indiceLettre,mot)),-self.dPool.id((y,z,lettre)), self.ePool.id((y,z,indiceLettre+1,mot))])

    def chemin_se_suivent(self) :
        for mot in (self.pos+self.neg):    
            if mot != '':
                for y in range(self.k):
                    for z in range(self.k):
                        for indiceLettre in range(1,len(mot)):
                            d=[-self.ePool.id((y,z,indiceLettre,mot))]
                            for x in range(self.k):
                                d.append(self.ePool.id((x,y,indiceLettre-1,mot)))


    # def au_moins_une_transi(self):
    #     d = []
    #     for x in range(self.k):
    #         for y in range(self.k):
    #             for lettre in self.alphabet:
    #                 d.append(self.dPool.id((x,y,lettre)))
    #     self.cnf.append(d)
    
    def automate_complet(self):
        for x in range(self.k):
            for lettre in (self.alphabet) :
                d=[]
                for y in range(self.k) :
                    d.append(self.dPool.id((x,y,lettre)))
                self.cnf.append(d)

    def automate_reversible(self):
        for y in range(self.k):  # sommet d'arrivé
            for lettre in (self.alphabet):
                for x1 in range(self.k) :  # sommet de départ 1
                    for x2 in range(self.k) :  # sommet de départ 2
                        if x1 != x2 :
                            self.cnf.append([-self.dPool.id((x1,y,lettre)), -self.dPool.id((x2,y,lettre))])

    def au_plus_ell_etats_acceptant(self):
        d = []
        for x in range(self.k) : # sommet           
            d.append(self.fPool.id((x)))
        atmost = [d,self.ell]
        self.cnf.append(atmost, is_atmost=True)

    
    def etat_final(self):
        for mot in self.pos:
            for x in range(self.k):
                for y in range(self.k):
                    lettre = mot[-1]
                    self.cnf.append(-self.ePool.id((x,len(mot)-1,mot)),-self.dPool.id((x,y,lettre)),self.etatFinal.id((y,mot)))   

    def solve_aut(self):
        s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
        #s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
        s.append_formula(self.cnf.clauses, no_return=False)
        # s.append_formula(self.cnf.atmosts, no_return= False)
        resultat = s.solve()
        interpretation = s.get_model()
        if resultat :
            self.interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
        print(self.interpretation_filtree)
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
                        self.cnf.append([-self.ePool.id((x,i,mot)),-self.dPool.id((x,y,lettre)),-self.fPool.id((y)), self.finalPool.id((x,y,mot))])
                        self.cnf.append([-self.finalPool.id((x,y,mot)),self.dPool.id((x,y,lettre))])
                        self.cnf.append([-self.finalPool.id((x,y,mot)),self.ePool.id((x,i,mot))])
                    else:
                        self.cnf.append([self.fPool.id((0))])
                

    def etat_final_implique_etat_acceptant (self) :
        for x in range(self.k):
            for mot in self.pos:
                for y in range(self.k):
                    self.cnf.append([-self.finalPool.id((x,y,mot)),self.fPool.id((y))])

    
    def au_moins_un_etat_acceptant(self):
        for mot in self.pos:
            if mot!='':
                d = []
                for x in range(self.k) : # sommet  
                    for y in range(self.k) :         
                        d.append(self.finalPool.id((x,y,mot)))
                self.cnf.append(d)

    def lien_chemin_transition(self):
        # Lien entre chemin et transition :
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for mot in (self.pos+self.neg):
                    for indiceLettre in range(len(mot)-1):
                        lettre = mot[indiceLettre]
                        self.cnf.append([-self.ePool.id((x, indiceLettre, mot)), self.ePool.id((y, indiceLettre+1, mot)), -self.dPool.id((x,y,lettre))])
    
    def autre_sens(self):
        for x in range(self.k):  # x = transition initiale
            for y in range(self.k):  # y  = transition finale
                for mot in (self.pos+self.neg):
                    for indiceLettre in range(1,len(mot)):
                        lettre = mot[indiceLettre]
                        self.cnf.append([-self.ePool.id((y, indiceLettre, mot)), self.ePool.id((x, indiceLettre-1, mot)), -self.dPool.id((x,y,lettre))])

    
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
    a.exec_finie_etat_acceptant()  # Exécution finie sur état acceptant
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    a.existe_un_chemin_mots_acceptants()  # Il faut qu'il existe un chemin pour les mots acceptants
    a.une_seule_transition_possible()  # Une seule transition possible
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()
    a.chemin_se_suivent()
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
        a.une_seule_transition_possible()  # Une seule transition possible
        a.existe_un_chemin_mots_acceptants()  # Il faut qu'il existe un chemin pour les mots acceptants
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
    a.une_seule_transition_possible()  # Une seule transition possible
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
    a.une_seule_transition_possible()  # Une seule transition possible
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
    a.existe_un_chemin_mots_acceptants()
    a.transition_implique_chemin()  # Transition implique chemin
    a.exec_finie_etat_non_acceptant()  # Exécution finie sur état non-acceptant
    a.lien_etat_final_transition()
    a.etat_final_implique_etat_acceptant()
    a.au_moins_un_etat_acceptant()
    a.lien_chemin_transition()
    a.autre_sens()
    resultat = a.solve_aut() 
    return a.create_nfa(resultat)

def main():
    test_aut()
    # test_minaut()
    # test_autc()
    # test_autr()
    # test_autcard()
    # test_autn()

if __name__ == '__main__':
    main()

