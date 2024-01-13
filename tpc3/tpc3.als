// Recall the hash table Alloy model,
// now with mutable lists inside the buckets.

sig Bucket {
	var head : lone Node // head: (bucket,node)
}
sig Node {
	key : one Key,
	var prox : lone Node
}
sig Key {
	hash : one Hash
}
sig Hash {}

// Specify the operation of inserting a node
// in the hash table. The node should be 
// inserted at the head of a bucket.
// If the operation only works well when the
// hash of the new node does not exist in the
// table you get Two points. If it always 
// works well you get Five points. Use the
// respective commands to check how many
// points you have.


// Predicado que verifica se a hash de um certo node existe.
pred existsHash[n: Node]{
  some b: Bucket | b.head.key.hash = n.key.hash and b.head.*prox.key.hash = n.key.hash
}

// Devolve o Bucket que tem a hash do node fornecido.
fun bucketWithHash[n: Node]: Bucket {
	{b: Bucket | b.head.key.hash = n.key.hash and b.head.*prox.key.hash = n.key.hash}
}
 

pred insert[n : Node] {
  
  // Hash ainda não existe
  not existsHash[n] => (one b: Bucket | head' = head + b->n and prox' = prox)

  // Hash já existe
  existsHash[n] => (one b: bucketWithHash[n] | head' = head - (b->b.head) + b->n and prox' = prox + n->b.head)

  // O prox resultante da inserção não é cíclico
  n not in n.^(prox')

}