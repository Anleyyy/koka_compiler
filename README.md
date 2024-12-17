# Koka-compiler
Lexer:

La création du lexer n'a pas été la partie la plus difficile. La réelle difficulté était dans la gestion de l'indentation. Celle-ci est faite par la fonction next_token en utilisant l'algorithme décrit dans le sujet. La fonction next_token ajoute les lexèmes ";", "{" et "}" manquants  lorqu'il y a de l'indentation et crée une file correspondant aux prochains lexèmes à renvoyer.  
A chaque appel de la fonction next_token on renvoie le prochain lexème de la file et dès que la file est vide on appel la fonction next_tokens du lexer pour la reremplir.

Parser:  
Une fois le parser implémenté à partir des règles de la grammaire définies dans le sujet, le parser renvoyait systématiquement un arbre vide. En effet, l'utilisation de "separated_list(SCOLON,decl) SCOLON*" dans la règle file posait problème puisque tant que l'on avait des tokens SCOLON, menhir essayait de trouver des decl ensuite sans jamais passer à SCOLON*. Ainsi, on a rajouté une règle decl_list qui permet de chercher des decl en priorité. Le même problème est apparu pour les stmt et les block et il a été résolu de la même façon.  
Il reste toujours des conflits mais nous n'avons détecté aucun comportement problématique et l'ordre indiqué dans les règles semblent toujours permettre d'avoir le comportement indiqué. Par exemple l'expression return 5 + 8 sera bien comprise comme return (5+8) et non pas (return 5) + 8 en raison de l'ordre dans le fichier parser.mly. En revanche cela apparait toujours comme un conflit.   
Les erreurs pourraient être plus précise. Plusieurs situations ne font toujours pas l'objet d'erreur précise bien que certaines règles ont été rajouté dans la grammaire pour détecter des erreurs précises. Nous avons fait le choix d'ailleurs d'utiliser ce moyen la pour avoir des erreurs plus pertinentes. En effet nous avons remarqué en utilisant le compilateur de koka fourni par le langage que les erreurs de syntaxe avait pour message d'erreur les règles ou token possibles après un certain état. Nous avons choisi de ne pas récupérer l'état actuel de l'automate de menhir et d'afficher les différentes transitions extérieures possibles mais de privilégier le cas par cas en rajoutant des règles dans la grammaire. Cependant toutes les règles possibles n'ont pas encore été implémentées et par conséquent certaines situations donnent lieux à des messages d'erreurs très vagues. 

Typeur:

Solution pour gérer l'inférence de type :  

Nous avons créé deux types ocaml qui correspondent aux types de calcul de koka : le type calctype et le type ucalctype.  
L'arbre en sortie du typeur est décoré avec des types de type calctype et les types de type ucalctype sont juste une étape intermédiaire permettant de gérer l'inférence de type.  
Ainsi les décorations a_utyp, utyp et b_utyp ne servent qu'à l'intérieur du typeur. La production de code n'utiliseras que les décorations a_typ, typ et b_typ.  
Un type de calcul koka correspond à un couple (type de valeur, effet), il en est de même pour les types ocaml correspondants.  
Nous avons donc deux types ocaml correspondant aux types de valeur de koka : valtype et uvaltype ainsi que deux types ocaml correspondant aux effets de koka : effect et ueffect.  
valtype correspond à un type de valeur standard de koka ou potentiellement un type faible "Vweak" notamment dans le cas des listes vide.  
uvaltype donne en plus la possibilité d'avoir un type "Mutable" dont on ne connait pas encore le type et dont le type sera découvert plus tard dans le typage.  
effect correspond à un effet standard de koka.  
ueffect donne en plus la possibilité d'avoir un effet "Emutable" qui correspond à l'union d'un effet koka avec l'effet de la fonction de type fun que l'on est entrain de typer, cela s'avère utile lors d'appels récursifs de la fonction car on ne connaît pas l'effet que va renvoyer la fonction à l'avance.  

Architecture globale :

La fonction type_file prend en paramètre l'ast de type file (décoré par les localisations) obtenu après le parsing et renvoie un ast de type tfile décoré par les types.

On type alors le programme déclaration par déclaration en appelant la fonction type_fb qui prend en paramètre :  
- loc : localisation de la déclaration  
- fun_decl : un booléen vrai si on appelle type_fb pour typer une déclaration de type fun et faux si on appelle type_fb pour typer une déclaration de fonction anonyme  
- le corps de lafonction de type funbody  
- l'environnement dans lequel est définie la fonction  

Au cours du typage de la déclaration d'une fonction f de type fun, on conserve des informations globales dans la variable f_env :  
- le nom de la fonction f_env.id  
- un dictionnaire f_env.weakvalenv qui prend comme clefs les identifiants des types à inférer et comme valeurs la valeur de type uvaltype inférée jusqu'à présent  
- une liste d'effets f_env.expected_effect qui correspond aux effets possibles que peut renvoyer la fonction de type fun que l'on est entrain de traîter  
- f_env.next_weakval : l'identifiant du prochain type à inférer qui sera créé  
- f_env.post_verif : un dictionnaire qui permet de gérer des vérifications à faire à posteriori dans le cadre des règles d'inférence 9, 11, 12 et 24  
- f_env.return_pile : une pile dont l'élément du dessus correspond au type de retour de la fonction la plus profonde dans laquelle on se situe  

Tout au long du typage d'une fonction, on utilise uniquement le type ucalctype et on décore l'ast avec les types de type ucalctype. C'est le rôle des fonctions type_expr, type_bexpr et type_atom qui parcourent l'arbre en appliquant les règles d'inférence.  
Une fois qu'on a traité une déclaration de fonction, les types qui devaient être inférés l'ont été. On parcours alors à nouveau l'ast en décorant cette fois ci l'ast avec les types de type calctype que l'on obtient à partir du type ucalctype.  

Choix effectués :

On privilégie toujours l'environnement local, si une fonction a été déclaré avec le nom f et qu'une fonction (anonyme ou non) est ensuite déclarée avec un paramètre nommé f, la fonction f n'existera pas dans cet environnement.  
De manière similaire si une fonction (anonyme ou no) possède un paramètre x et qu'une fonction anonyme est définie à l'intérieur avec un paramètre nommé x, dans l'environnement de la seconde fonction seul son propre paramètre existera.  
Il en est de même pour les variables dans des blocs imbriqués ou  pour des variables et des paramètres de fonction ayant le même nom, on garde toujours uniquement l'identifiant le plus local.  

Difficultés rencontrées :

La gestion de l'inférence de type a demandé une longue période de recherche pour trouver une solution efficace. Le typage du langage demande une assez bonne compréhension de celui-ci ce qui demande un certain temps. Nous avons aussi sous-estimé le temps nécessaire au débuggage du typeur.
