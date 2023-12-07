#!/usr/bin/env python3.6
# cours informatique fondamentale 2021-2022
# chapitre SAT
# probleme du Sudoku

# il faut passer en argument la dimension d'un sous-carre et optionnellement le nom du fichier contenant la grille de depart
# exemple 'python sudoku.py 3 grilles/9/evil' va prendre la grille evil de dimension 9x9 et la resoudre 
# 'python sudoku.py 6' va generer une solution a une grille vide de dimension 36x36

from pysat.solvers import Minisat22
from pysat.solvers import Glucose4
from pysat.formula import CNF
from pysat.formula import IDPool
import sys
import re

######### parametres #########################
c = int(sys.argv[1]) # dimension d'un sous-carre
affichage_sol = True # affichage d'une solution
test_unicite = True # test si la solution est unique (si elle existe), sinon en donne une autre

######### variables ##########################
vpool = IDPool(start_from=1) # pour le stockage des identifiants entiers des couples (i,j)
cnf = CNF()  # construction d'un objet formule en forme normale conjonctive (Conjunctive Normal Form)
n = c*c # dimension de la grille


# construction de la formule

print("Construction des clauses\n")

if len(sys.argv) > 2:

    print("Valeurs initiales")

    with open(sys.argv[2]) as f:
        contents = f.read()

        # le code suivant permet de creer a partir du fichier une matrice de chaine de caracteres qui correspond a la grille donnee en entree
        
        contents_lines = contents.split("\n")
        contents_split = map(lambda l: l.split(' '),contents_lines)
        matrix = list(map(lambda l: list(filter(lambda x : x!='', l)), contents_split))

        # on peut alors ajouter les contraintes
        
        for i in range(n):
            for j in range(n):
                e = matrix[i][j]
                match = re.search(r'\d+', e) # verifie que l'entree est une sequence de chiffres
                if match:
                    v = int(e)
                    # print("ajout de %1d pour (%1d,%1d)" % (v,i,j)) 
                    cnf.append([vpool.id((i,j,v))]) # ajout d'une liste ne contenant qu'un seul literal
                

# au moins une valeur par case
print("Au moins un nombre par case")

for i in range(n):
    for j in range(n):
        d = []
        for v in range(n):
            d.append(vpool.id((i,j,v+1)))
        cnf.append(d)


# pas de doublons sur les lignes

print("Pas de doublons sur les lignes")

for i in range(n):
    for j in range(n):
        for k in range(j+1,n):
            for v in range(n):
                cnf.append([-vpool.id((i,j,v+1)),-vpool.id((i,k,v+1))])


# pas de doublons sur les colonnes

print("Pas de doublons sur les colonnes")

for i in range(n):
    for j in range(n):
        for k in range(j+1,n):
            for v in range(n):
                cnf.append([-vpool.id((j,i,v+1)),-vpool.id((k,i,v+1))])


# pas de doublons sur les carres

print("Pas de doublons sur les carres")

# on identifie un carre par une paire (d1,d2) dans {0,...,c-1} x {0,...,c-1}

for d1 in range(c):
    for d2 in range(c):
        for i1 in range(c):
            for i2 in range(c):
                for j1 in range(c):
                    for j2 in range(c):
                        if (i1+d1*c != i2+c*d1) or (j1+c*d2 != j2+c*d2):
                            for v in range(n):
                                cnf.append([-vpool.id((i1+d1*c,j1+d2*c,v+1)),-vpool.id((i2+c*d1,j2+c*d2,v+1))])
                            

# au plus une valeur par case (contrainte pas necessaire car elle est une consequence des autres)
# permet d'accelerer la resolution

# print("Au plus une valeur par case")

for i in range(n):
    for j in range(n):
        for v1 in range(n):
            for v2 in range(v1+1,n):
                cnf.append([-vpool.id((i,j,v1+1)),-vpool.id((i,j,v2+1))])


print(cnf.clauses) # pour afficher les clauses


# phase de resolution

s = Minisat22(use_timer=True) # pour utiliser le solveur MiniSAT
# s = Glucose4(use_timer=True) # pour utiliser le solveur Glucose
s.append_formula(cnf.clauses, no_return=False)

print("Resolution...")
resultat = s.solve()
print("Satisfaisable : " + str(resultat))
print("Temps de resolution : " + '{0:.2f}s'.format(s.time()))

# affichage solution

def affichage_solution(interpretation):
    

    for i in range(n):
        if (i % c) == 0 and i != 0:
            for j in range(n+c-1):
                print("---",end='')
            print("")
        for j in range(n):
            for v in range(n):
                if vpool.id((i,j,v+1)) in interpretation_filtree: # la repetition de cette etape prend du temps si on ne filtre pas avant
                    if (j % c) == 0 and j !=0:
                        print(" | %2d " % (v+1),end='')
                    else:
                        print("%2d " % (v+1),end='')
        print("")

        
if affichage_sol and resultat:
    print("\nVoici une solution: \n")
    interpretation = s.get_model()
    # cette interpretation est longue, on va filtrer les valeurs positives (il y a en n fois moins)
    interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
    affichage_solution(interpretation_filtree)


    # test d'unicite
    if test_unicite:
        d = []
        for i in range(n):
            for j in range(n):
                for v in range(n):
                    if vpool.id((i,j,v+1)) in interpretation_filtree:
                        d.append(-vpool.id((i,j,v+1)))
        s.add_clause(d)
        not_unique = s.solve() # solution pas unique si la formule est satisfaisable
        if not not_unique:
            print("Solution unique")
        else:
            print("\nSolution pas unique, en voici une autre:\n")
            interpretation = s.get_model()
            # cette interpretation est longue, on va filtrer les valeurs positives (il y a en n fois moins)
            interpretation_filtree = list(filter(lambda x : x >=0, interpretation))
            affichage_solution(interpretation_filtree)
