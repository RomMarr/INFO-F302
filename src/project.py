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
        self.etatPool = IDPool(start_from=1)    # Variable pour l'existance des états de l'automate 
        self.FPool = IDPool(start_from=k+1)     # Variable pour les états acceptant de l'automate
        self.transiPool = IDPool(start_from=2*k+1)  # Variable pour les transitions de l'automate
        self.execPool = IDPool(start_from=2*k+(k**2)*len(alphabet)+1)   # Variable pour les exécutionw des mots de l'automate

        if ell == -1 :
            self.cnf = CNF()  # construction d'un objet formule, en forme normale conjonctive (Conjunctive Normal Form)
        else:
            self.cnf = CNFPlus()  # CNFPlus permet d'ajouter des contraintes sur la cardinalité (question 6)
        
        self.alphabet = alphabet  # Alphabet de l'automate
        self.pos = pos  # Mots devant avoir une execution acceptante
        self.neg = neg  # Mots ne devant pas avoir d'execution acceptante
        self.k = k  # Nombre maximal d'état de l'automate
        self.ell = ell  # Nombre maximal d'état acceptant (question 6)
        self.interpretation_filtree = None

    # Fonctions de création des clauses :
    def existance_etat_initial(self):
        """ Existence de l'état initial """ 
        self.cnf.append([self.etatPool.id((0))])

    def transition_valide(self):
        """ 
        Chaque transition doit être valide, il faut donc que l'état initial et final de la transition existe
        """
        for i in self.alphabet:
            for x in range(self.k):  # x = état initial
                for y in range(self.k):  # y  = état final
                    self.cnf.append([-self.transiPool.id((x,y,i)), self.etatPool.id((y))])  # Existance état final
                    self.cnf.append([-self.transiPool.id((x,y,i)), self.etatPool.id((x))])  # Existance état initial

    def mot_commence_0(self):
        """ Tout mot commence à 0 """
        for mot in (self.pos + self.neg):
            self.cnf.append([self.execPool.id((0,0,mot))])

    def exec_finit_etat_non_acceptant(self):
        """" L'exécution des mots de neg ne finissent pas, ou finissent sur des états non-acceptants """
        for x in range(self.k):  # x = état initial
            for y in range(self.k):  # y  = état final
                for mot in self.neg:
                    if mot != '' :
                        lettre = mot[-1]  # Dernière lettre de mot
                        i = len(mot)-1  # Indice de la dernière lettre de mot
                        self.cnf.append([-self.execPool.id((x,i,mot)),-self.transiPool.id((x,y,lettre)),-self.FPool.id((y))])
                    else :
                        self.cnf.append([-self.FPool.id((0))])

    def exec_finit_etat_acceptant(self):
        """ L'exécution des mots de pos finissent tous sur des états acceptants """
        for x in range(self.k):  # x = état initial
            for y in range(self.k):  # y  = état final
                for mot in self.pos:
                    if mot != '' :
                        lettre = mot[-1]    # Dernière lettre de mot
                        i = len(mot) - 1    # Indice de la dernière lettre de mot
                        self.cnf.append([-self.execPool.id((x,i,mot)),-self.transiPool.id((x,y,lettre)),self.FPool.id((y))])
             
    def existe_un_chemin_mots_acceptants(self):
        """ Chaque mot de pos doit avoir un chemin bien défini à chacunes de ses lettres"""
        for mot in (self.pos):
            for indiceLettre in range(len(mot)):
                d = [] 
                for x in range(self.k):  # Etétatat initial
                    d.append(self.execPool.id((x, indiceLettre, mot)))
                self.cnf.append(d)    
                    
    def unicite_transition(self):
        """  Il ne peut pas y avoir deux transitions différentes qui partent du même état avec la même lettre """
        for x in range(self.k):  # x = état initial
            for y in range(self.k):  # y  = état final 1 
                for z in range(self.k):  # y  = état final 2
                    if z != y:
                        for lettre in self.alphabet:
                            self.cnf.append([-self.transiPool.id((x,y,lettre)), -self.transiPool.id((x, z, lettre))])

    def chemin_implique_transition(self):
        """ Un chemin passant sur un état implique une transition vers un autre état pour les mots de pos """
        for x in range(self.k):  # x = état initial
            for mot in (self.pos):
                for indiceLettre in range(len(mot)):
                    d=[]
                    d.append(-self.execPool.id((x, indiceLettre, mot)))
                    for y in range(self.k):
                        lettre = mot[indiceLettre]
                        d.append(self.transiPool.id((x,y,lettre)))
                    self.cnf.append(d)

    def transition_implique_chemin(self):
        """ Une transition entre deux états implique l'existance d'un chemin si le mot passe par le premier état """
        for x in range(self.k): # état initial
            for y in range(self.k): # état final
                for mot in (self.pos+self.neg):
                    for indiceLettre in range(len(mot)-1):
                        lettre = mot[indiceLettre]
                        self.cnf.append([-self.transiPool.id((x,y,lettre)), -self.execPool.id((x,indiceLettre,mot)), self.execPool.id((y,indiceLettre+1,mot))])

    def automate_complet(self):
        """ Pour qu'un automate soit complet il faut que chaque sommet ait une transition pour chaque lettre """
        for x in range(self.k):  # état initial
            for lettre in (self.alphabet) :
                d=[]
                for y in range(self.k) :
                    d.append(self.transiPool.id((x,y,lettre)))
                self.cnf.append(d)

    def automate_reversible(self):
        """ Pour qu'un automae soit reversible, il ne faut pas que deux états différents aient une transition vers le
        même état avec la même lettre """
        for y in range(self.k):  # état d'arrivé
            for lettre in (self.alphabet):
                for x1 in range(self.k) :  # état de départ 1
                    for x2 in range(self.k) :  # état de départ 2
                        if x1 != x2 :
                            self.cnf.append([-self.transiPool.id((x1,y,lettre)), -self.transiPool.id((x2,y,lettre))])

    def au_plus_ell_etats_acceptant(self):
        """ Contrainte sur la cardinalité des états acceptants pour pas qu'il y en ait plus que ell (= l) """
        d = []
        for x in range(self.k) : # état initial           
            d.append(self.FPool.id((x)))  # Ajoute chaque état acceptant à d
        atmost = [d,self.ell]   
        self.cnf.append(atmost, is_atmost=True) # Ajoute la contrainte de cardinalité


    def solve_aut(self):
        """ Méthode de résolution du solveur Sat """
        s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
        #s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
        s.append_formula(self.cnf.clauses, no_return=False) # Ajout des clauses
        resultat = s.solve()
        interpretation = s.get_model()
        if resultat :
            self.interpretation_filtree = list(filter(lambda x : x >=0, interpretation))    # Ne récupère que les valeurs positives                                                     
        return resultat
    
    def solve_autcard(self) :
        """ Méthode de résolution du solveur Sat pour la question 6 """
        s = Minicard(use_timer=True)  # pour utiliser le solveur Minicard (seulement pour la question 6)
        s.append_formula(self.cnf.clauses, no_return=False)   # Ajout des clauses
        s.append_formula(self.cnf.atmosts, no_return= False)  # Ajout des contraintes de cardinalité
        resultat = s.solve()
        interpretation = s.get_model()
        if resultat :
            self.interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
        return resultat
    


    # Fonction de création d'automates (DFA) à partir des clauses : 
    def create_dfa(self, resultat) -> DFA:
        """ Crée un automate fini déterminisite à partir des clauses et du résultat du solveur """
        states = set()  # Set contenant les états de l'automate
        transitions = dict()    # Dictionnaire contenant les transitions de l'automate
        accepting = set()   # Set contenant les états acceptants de l'automate
        
        if not resultat:
            return None # Si le solveur n'a pas trouvé de solution
        
        bornEtat = self.k+1 # Il y a maximum k états à l'automate
        bornF = 2*self.k+1  # Il y a maximum k états acceptants à l'automate donc on l'ajoute à la borne
        bornTransi = 2*self.k+(self.k**2)*len(self.alphabet)+1   # Il y a maximum (k**2)*len(alphabet) transitions
        for soluce in self.interpretation_filtree : # Boucle sur toutes les clauses positives
            if soluce < bornEtat:
                states.add('q'+str(soluce-1))   # Ajoute tous les états au set
            elif soluce < bornF:
                accepting.add('q'+str(soluce-self.k-1)) # Ajoute tous les état acceptants au set
            elif soluce < bornTransi :
                sommetDepart = 'q'+str(((soluce-2*self.k-1)//self.k)%self.k)   # Indice de l'état de départ
                lettre = self.alphabet[(soluce-2*self.k-1)//self.k**2]  # Indice de la lettre
                sommetArive = 'q'+str((soluce-2*self.k-1)%self.k)   # Indice de l'état d'arrivé
                if sommetDepart not in transitions: # Si l'état n'a pas encore de dictionnaire de transition, il est initialisé
                    temp =  dict()
                    temp[lettre] = sommetArive
                else :
                    temp = transitions[sommetDepart]  # Sinon la transition est juste ajoutée au dictionnaire
                    temp[lettre] = sommetArive
                transitions[sommetDepart] = temp
        for sommet in states :  # S'assure que tous les états ont bien un dictionnaire de transition, même vide
            if sommet not in transitions:
                transitions[sommet] = dict()
        return DFA(states=states, input_symbols=set(self.alphabet), transitions =transitions, initial_state ="q0", final_states = accepting, allow_partial=True)
    
                        

class AutomateNFA(Automate):
    def __init__(self, alphabet: str, pos: list[str], neg: list[str], k: int, ell = -1):
        self.finalPool = IDPool(start_from= 1000)   # Variable représentant les état finaux acceptants des mots
        super().__init__(alphabet,pos,neg,k,ell)
    

    def lien_etat_final_transition(self) :
        """ Lien entre la nouvelle variable état final et les transitions"""
        for x in range(self.k):  # état initial
            for y in range(self.k):  # état final 
                for mot in self.pos:
                    if mot != "":
                        lettre = mot[-1]   # Dernière lettre du mot
                        i = len(mot)-1  # Indice de la dernière lettre du mot
                        self.cnf.append([-self.execPool.id((x,i,mot)),-self.transiPool.id((x,y,lettre)),-self.FPool.id((y)), self.finalPool.id((x,y,mot))])
                        self.cnf.append([-self.finalPool.id((x,y,mot)),self.transiPool.id((x,y,lettre))])
                        self.cnf.append([-self.finalPool.id((x,y,mot)),self.execPool.id((x,i,mot))])
                    else:
                        self.cnf.append([self.FPool.id((0))])
                

    def etat_final_implique_etat_acceptant (self) :
        """  Existance de la variable etat final implique que l'état associé soit acceptant """
        for x in range(self.k): # état précédant l'état final
            for mot in self.pos:
                for y in range(self.k): # état final
                    self.cnf.append([-self.finalPool.id((x,y,mot)),self.FPool.id((y))])

    
    def au_moins_un_etat_acceptant(self):
        """ Tous les mots de pos doivent avoir au moins un état acceptant"""
        for mot in self.pos:
            if mot!='':
                d = []
                for x in range(self.k) : # état précédant l'état final  
                    for y in range(self.k) : # Etat final   
                        d.append(self.finalPool.id((x,y,mot)))
                self.cnf.append(d)
    
    def lien_chemin_transition(self):
        """ Lien entre chemin et transition :
        Cette méthode n'est pas la bonne car elle met trop de contrainte sur l'automate NFA, en obligeant tous les
        états consécutifs à être reliés par une transition. Cependant nous n'avons pas réussi à trouver une manière
        de faire le lien entre les executions des mots et les transitions moins contraignantes.
        """
        for x in range(self.k):  # état initial
            for y in range(self.k):  # état final
                for mot in (self.pos+self.neg):
                    for indiceLettre in range(len(mot)):
                        lettre = mot[indiceLettre]
                        self.cnf.append([-self.execPool.id((x, indiceLettre, mot)), -self.execPool.id((y, indiceLettre+1, mot)), self.transiPool.id((x,y,lettre))])


    
    def create_nfa(self, resultat):
        """ Crée un automate fini non-déterminisite à partir des clauses et du résultat du solveur 
        Même principe que pour le DFA mais il faut ici créer des sets d'états pour chaque lettres """
        states = set()  # Set contenant les états de l'automate
        transitions = dict()  # Dictionnaire contenant les transitions de l'automate
        accepting = set()  # Set contenant les états acceptants de l'automate
        
        if not resultat:
            return None  # Si le solveur n'a pas trouvé de solution
        
        bornEtat = self.k+1  # Il y a maximum k états à l'automate
        bornF = 2*self.k+1   # Il y a maximum k états acceptants à l'automate donc on l'ajoute à la borne
        bornTransi = 2*self.k+(self.k**2)*len(self.alphabet)+1  # Il y a maximum (k**2)*len(alphabet) transitions
        for soluce in self.interpretation_filtree : # Boucle sur toutes les clauses positives
            if soluce < bornEtat:
                states.add('q'+str(soluce-1))   # Ajoute tous les états au set
            elif soluce < bornF:
                accepting.add('q'+str(soluce-self.k-1)) # Ajoute tous les état acceptants au set
            elif soluce < bornTransi :
                sommetDepart = 'q'+str(((soluce-2*self.k-1)//self.k)%self.k)    # Indice de l'état de départ
                lettre = self.alphabet[(soluce-2*self.k-1)//self.k**2]  # Indice de la lettre
                sommetArive = 'q'+str((soluce-2*self.k-1)%self.k)   # Indice de l'état d'arrivé
                if sommetDepart not in transitions: # Si l'état n'a pas encore de dictionnaire de transition, il est initialisé  
                    temp =  dict()
                    temp[lettre] = {sommetArive}    # Ici on initialise le set
                else :
                    temp = transitions[sommetDepart]    # Sinon la transition est juste ajoutée au dictionnaire
                    temp[lettre] = temp.get(lettre,set())
                    temp[lettre].add(sommetArive)
                transitions[sommetDepart] = temp
        for sommet in states :  # S'assure que tous les états ont bien un dictionnaire de transition, même vide
            if sommet not in transitions:
                transitions[sommet] = dict()
        return NFA(states=states, input_symbols=set(self.alphabet), transitions =transitions, initial_state ="q0", final_states =accepting)

# Q2
def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  # Existance état initial
    a.transition_valide()  # Transition valide  
    a.mot_commence_0()  # Tout mot commence à 0          
    a.chemin_implique_transition()   # Chemin implique transition
    a.transition_implique_chemin()  # Transition implique chemin
    a.unicite_transition()  # Un seul chemin possible
    a.existe_un_chemin_mots_acceptants()  # Il faut qu'il existe un chemin pour les mots acceptants
    a.exec_finit_etat_acceptant()  # Exécution finit sur état acceptant
    a.exec_finit_etat_non_acceptant()  # Exécution finit sur état non-acceptant
    resultat = a.solve_aut()
    return a.create_dfa(resultat)
    
# Q3
def gen_minaut(alphabet: str, pos: list[str], neg: list[str]) -> DFA:
    k = 1   # Initialise k à 1
    resultat = False    # Initialise le résultat à False
    
    while not resultat :    # Boucle tant qu'aucune solution n'est trouvée en incrémentant k à chaque fois
        a = Automate(alphabet, pos, neg, k)
        a.existance_etat_initial() 
        a.transition_valide() 
        a.mot_commence_0()  
        a.chemin_implique_transition()   
        a.transition_implique_chemin()  
        a.unicite_transition()  
        a.existe_un_chemin_mots_acceptants()  
        a.exec_finit_etat_acceptant() 
        a.exec_finit_etat_non_acceptant() 
        resultat = a.solve_aut()
        k+=1
    return a.create_dfa(resultat)

# Q4
def gen_autc(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  
    a.transition_valide()  
    a.mot_commence_0()  
    a.chemin_implique_transition()   
    a.transition_implique_chemin()  
    a.unicite_transition()  
    a.exec_finit_etat_acceptant() 
    a.exec_finit_etat_non_acceptant()  
    a.automate_complet()  # Clause permettant de vérifier si l'automate est complet
    resultat = a.solve_aut()
    return a.create_dfa(resultat)

# Q5
def gen_autr(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    a = Automate(alphabet, pos, neg, k)
    a.existance_etat_initial()  
    a.transition_valide()  
    a.mot_commence_0()  
    a.chemin_implique_transition()   
    a.transition_implique_chemin()  
    a.unicite_transition()  
    a.exec_finit_etat_acceptant()  
    a.exec_finit_etat_non_acceptant() 
    a.automate_reversible()  # Clause permettant de vérifier si l'automate est réversible
    resultat = a.solve_aut() 
    return a.create_dfa(resultat)

# Q6
def gen_autcard(alphabet: str, pos: list[str], neg: list[str], k: int, ell: int) -> DFA:
    a = Automate(alphabet, pos, neg, k, ell)
    a.existance_etat_initial()  
    a.transition_valide() 
    a.mot_commence_0()  
    a.chemin_implique_transition()   
    a.transition_implique_chemin()  
    a.unicite_transition() 
    a.exec_finit_etat_acceptant()  
    a.exec_finit_etat_non_acceptant()  
    a.au_plus_ell_etats_acceptant()  # Clause permettant de vérifier si l'automate a au plus 'ell' états accpetants
    resultat = a.solve_autcard() 
    return a.create_dfa(resultat)

# Q7
def gen_autn(alphabet: str, pos: list[str], neg: list[str], k: int) -> NFA:
    a = AutomateNFA(alphabet, pos, neg, k)
    a.existance_etat_initial() 
    a.mot_commence_0()  
    a.transition_valide()
    a.existe_un_chemin_mots_acceptants()
    a.transition_implique_chemin() 
    a.exec_finit_etat_non_acceptant()  
    a.lien_etat_final_transition()  # Contraintes sur les états finaux
    a.etat_final_implique_etat_acceptant()  # Lien entre états finaux et etats acceptants
    a.au_moins_un_etat_acceptant()  # Clauses vérifiant que chaque mot de pos finit au moins une fois sur un état acceptant
    a.lien_chemin_transition()  # Clauses vérifiant les interactions entre les variables de chemins et celles de transitions
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
