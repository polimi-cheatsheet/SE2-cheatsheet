-- show predicate
pred show {}
-- will try to find an example
run show for 3 but 1 Book

pred show2[b: Book] {
    #b.addr > 1
    #Name.(b.addr) > 1
}

-- dynamic analysis
pred add[b, b': Book, n: Name, a: Addr] {
    b'.addr = b.addr + n -> a
}
pred showAdd[b,b': Book, n: Name, a: Addr] {
    add[b, b', n, a]
    #Nmae.(b'.addr) > 1
}
run showAdd

-- assertations and counterexamples
assert delUndoesAdd {
    all b, b', b'': Book, n: Name, a: Addr |
        add[b, b', n, a] and del[b', b'', n] implies
            b.addr = b''.addr
}
-- will try to find a counterexample
check delUndoesAdd for 3

-- functions
fun lookup[b: Book, n: Name]: set Addr {
    n.(b.addr)
}
assert addLocal {
    all b,b': Book, n,n': Name, a: Addr |
        add[b,b',n,a] and n != n' implies
            lookup[b,n'] = lookup[b',n']
}

-- set operators
Name = {(N0), (N1), (N2)}
Alias = {(N1), (N2)}
Group = {(N0)}
RecUsed = {(N0), (N2)}

Alias + Group = {(N0), (N1), (N2)}
Alias & RecUsed = {(N2)}
Name - RecUsed = {(N1)}
RecUsed in Alias = false
RecUsed in Name = true
Name = Group + Alias = true

Name = {(N0), (N1)}
Addr = {(A0), (A1)}
Book = {(B0)}
Name->Addr = {(N0,A0),(N0,A1),(N1,A0),(N1,A1)}

-- dot join
p = {(a,b), (a,c), (b,d)}
q = {(a,d,c), (b,c,c), (c,c,c), (b,a,d)}
p.q = {(a,c,c),(a,a,d)}
   -- (a,b) . (b,c,c) => (a,c,c)
   -- (a,b) . (b,a,d) => (a,a,d)
   -- (a,c) . (c,c,c) => (a,c,c)
   -- match last col of p with first of q and remove them
-- box join
a[b] = b.a
-- for binary relations
~r = r transposed
^r = r + r.r + r.r.r + ...
*r = iden + ^r
Node = {(N0), (N1), (N2), (N3)}
next = {(N0, N1), (N1, N2), (N2, N3)}
~next = {(N1,N0), (N2,N1), (N3,N2)}
^next = {(N0, N1), (N1, N2), (N2, N3),
         (N0, N2), (N1, N3), (N0, N2)}
*next = {(N0, N0), (N1, N1), (N2, N2)} + ^next

-- restriction and override
Name = {(N0), (N1), (N2)}
Alias = {(N0), (N1)}
Addr = {(A0)}
address = {(N0, N1), (N1, N2), (N2, A0)}

address :> Addr = {(N2, A0)} -- range restriction
Alias <: address = {(N0, N1), (N1, N2)} -- domain restriction
address :> Alias = {(N0, N1)}
workAddress = {(N0, N1), (N1, A0)}
address ++ workAddress = {(N0, N1), (N1, A0), (N2, A0)} -- override
m' = m ++ (k -> v) -- update map with (k,v)

-- set definition
{n: Name | no n.^address & Addr}

-- if-else
f implies e1 else e2
-- let binding
all n: Name |
    let w = n.workAddress, a = n.address |
        (some w implies a = w else a = n.homeAddress)

-- enum
abstract sig Color {}
one sig GREEN extends Color {}
one sig RED extends Color {}
all s: Semaphore | s.color = RED

-- seq
sig Path { positions: seq Position }
p.positions -- Int -> Position
p.positions[i] -- access the i-th position
p.positions.inds -- set of all the indexes
univ.(p.positions) -- set of all the elements
(p.positions).hasDups -- true if there are duplicates
