# Koka-compiler
Lexer: \n
Parser:
Une fois le parser implémenté à partir des règles de la grammaire définis dans le sujet, le parser renvoyé systématiquement un arbre vide. En effet, l'utilisation de "separated_list(SCOLON,decl) SCOLON*" dans la règle file posait problème puisque tant que l'on avait des tokens SCOLON, menhir essayait de trouver des decl ensuite sans jamais passer à SCOLON*. Ainsi, on a rajouté une règle decl_list qui permet de chercher des decl en priorité. Le même problème est apparu pour les stmt et les block et il a été résolu de la même façon.
Il reste toujours des conflits mais nous n'avons détecté aucun comportement problématique et l'ordre indiqué dans les règles semble toujours permettre d'avoir le comportement indiqué. Par exemple l'expression return 5 + 8 sera bien comprise comme return (5+8) et non pas (return 5) + 8 en raison de l'ordre dans le fichier parser.mly. En revanche cela apparait toujours comme un conflit. 
Les erreurs pourraient être plus précise. Plusieurs situations ne font toujours pas l'objet d'erreur précise bien que certaines règles ont été rajouté dans la grammaire pour détecté des erreurs précises. Nous avons fait le choix d'ailleurs d'utiliser ce moyen la pour avoir des erreurs plus pertinentes. En effet nous avons remarqué en utilisant le compilateur de koka fourni par le langage que les erreurs de syntaxe avait pour message d'erreur les règles ou token possible après un certain état. Nous avons choisi de ne pas récupérer l'état actuel de l'automate de menhir et d'afficher les différentes transitions extérieures possible mais de privilégier le cas par cas en rajoutant des règles dans la grammaire. Cependant toutes les règles possibles n'ont pas encore été implémenté et par conséquent certaines situations donnent lieux à des messages d'erreurs très vague. 
Typer:
