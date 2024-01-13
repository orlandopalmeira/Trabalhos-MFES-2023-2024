// Specify the properties that characterize 
// hash tables using closed addressing (separate 
// chaining) for collision resolution.

// The points you will get is proportional to the 
// number of correct properties. To check how many
// points you have so far you can use the different
// commands. For example, if check Three is correct 
// you will have at least 3 points.
// The maximum is 5 points.

// Be careful to not overspecify! 
// If you specify a property that is not valid in 
// these hash tables you get 0 points, 
// even if you have some correct properties.
// To check if you are not overspecifying you can use 
// command NoOverspecification. If you have an invalid
// property this command will return a valid hash table 
// that you specification is not accepting.
  

sig Bucket {
	head : lone Node
}

sig Node {
	key : one Key,
	prox : lone Node
}

sig Key {
	hash : one Hash
}

sig Hash {}

pred Invs {
  	// Um nodo não pode apontar para si próprio. Nem directamente, nem através de um nodo que lhe esteja ligado de alguma forma. 
	all n: Node | n not in n.^(prox.prox)
  
  	// Dois nodes não podem ter a mesma key
  	all n1, n2: Node | n1.key = n2.key implies n1 = n2
  
  	// Uma key deve estar nalgum node
  	all k: Key | k in Node.key
  
  	// Um node deve ser head ou prox UMA e UMA SÓ vez.
  	all n: Node | one prox.n + head.n
  
  	// Todos os nodos dentro de um certo bucket têm de ter o mesmo hash. (b.head.*prox devolve todos os nodes dentro do bucket)
  	all b: Bucket, n1,n2: Node | n1 in b.head.*prox and n2 in b.head.*prox implies n1.key.hash = n2.key.hash
  
  	// O hash de um bucket tem de ser garantidamente diferente de qualquer outro bucket
  	all disj b1, b2: Bucket | no b1.head.*prox.key.hash & b2.head.*prox.key.hash 
}