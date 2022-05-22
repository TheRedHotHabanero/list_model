module list[Time]

open util/ordering[Time] as o

// o/nxt - not my
// this/nxt or nxt- my

// open elem_order[Time]
// there will be something like header file in c++ prog

// A signature in Alloy is similar to the signature of a schema
// in that it defines the vocabulary for the model.
var sig Node { var nxt: set Node }

var sig Root in Node {}

// fix the root by subtracting a set reachable nodes from the set of all nodes
fact
{
  always
  {
    Root = Node - Node.^nxt // all nodes that are reachable from some nodes
  }
}

fun nodes(list: Node) : Node
{
  list.*(nxt + ~nxt)
}

fun root(list: Node) : Node
{
  Root & list.nodes
}

// last elem with no next roots
fun last(list: Node) : Node
{
  { n: list.nodes | no n.nxt }
}

// validation requirements
pred valid(lst: Node)
{
  all n: lst.nodes
  {
    lone n.nxt
    lone nxt.n //prev in fact
    n not in n.^nxt
  }
  one lst.root
}

// all is valid when every single part is valid
pred all_valid()
{
  all n:Node | n.valid
}

// making one list from two, validating requirements
pred join(r1, r2: Root)
{
  no r1.nodes & r2.nodes
  let l1 = r1.last
  {
    nxt' = nxt + l1 -> r2
    Node' = Node
    Root' = Root - r2
  }
}

run
{
  all_valid
  some r1, r2 : Root | join[r1, r2]
  after always {nxt' = nxt and Node' = Node and Root' = Root}
} for 5

assert prop1
{
  always
  {
    {
      all_valid
      some disj r1, r2: Root | join[r1, r2]
    }
    implies
    {
      after all_valid
    }
  }
}
check prop1 for 5