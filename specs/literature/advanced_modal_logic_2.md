# Advanced Modal Logic


*
Preface

i

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

ADVANCED MODAL LOGIC
This chapter is a continuation of the preceding one, and we begin it at the
place where the authors of Basic Modal Logic left us about fteen years
ago. Concluding his historical overview, Krister Segerberg wrote: \Where
we stand today is dicult to say. Is the picture beginning to break up,
or is it just the contemporary observer's perennial problem of putting his
own time into perspective?" So, where did modal logic of the 1970s stand?
Where does it stand now? Modal logicians working in philosophy, computer
science, articial intelligence, linguistics or some other elds would probably
give di erent answers to these questions. Our interpretation of the history
of modal logic and view on its future is based upon understanding it as part
of mathematical logic.
Modal logicians of the First Wave constructed and studied modal systems
trying to formalize a few kinds of necessity-like and possibility-like operators. The industrialization of the Second Wave began with the discovery
of a deep connection between modal logics on the one hand and relational
and algebraic structures on the other, which opened the door for creating
many new systems of both articial and natural origin. Other disciplines|
the foundations of mathematics, computer science, articial intelligence,
etc.|brought (or rediscovered1) more. \This framework has had enormous
inuence, not only just on the logic of necessity and possibility, but in other
areas as well. In particular, the ideas in this approach have been applied
to develop formalisms for describing many other kinds of structures and
processes in computer science, giving the subject applications that would
have probably surprised the subject's founders and early detractors alike"
Barwise and Moss 1996]. Even two or three mathematical objects may lead
to useful generalizations. It is no wonder then that this huge family of logics
gave rise to an abstract notion (or rather notions) of a modal logic, which
in turn put forward the problem of developing a general theory for it.
Big classes of modal systems were considered already in the 1950s, say
extensions of S5 Scroggs 1951] or S4 Dummett and Lemmon 1959]. Completeness theorems of Lemmon and Scott 1977],2 Bull 1966b] and Segerberg
1971] demonstrated that many logics, formerly investigated \piecewise",
1 One of the celebrities in modal logic|the G
odel{Lob provability logic GL|was rst
introduced by Segerberg 1971] as an \articial" system under the name K4W.
2 This book was written in 1966.

2

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

have in fact very much in common and can be treated by the same methods. A need for a uniting theory became obvious. \There are two main
lacunae in recent work on modal logic: a lack of general results and a lack
of negative results. This or that logic is shown to have such and such a property, but very little is known about the scope or bounds of the property.
Thus there are numerous results on completeness, decidability, nite model
property, compactness, etc., but very few general or negative results", wrote
Fine 1974c]. The creation of duality theory between relational and algebraic
semantics (Lemmon 1966a,b], Goldblatt 1976a,b]), originated actually by
Jonsson and Tarski 1951], the establishment of the connection between
modal logics and varieties of modal algebras (Kuznetsov 1971], Maksimova
and Rybakov 1974], Blok 1976]), and between modal and rst and higher
order languages (Fine 1975b], van Benthem 1983]) added those mathematical ingredients that were necessary to distinguish modal logic as a separate
branch of mathematical logic.
On the other hand, various particular systems became subjects of more
special disciplines, like provability logic, deontic logic, tense logic, etc., which
has found reection in the corresponding chapters of this Handbook.
In the 1980s and 1990s modal logic was developing both \in width"
and \in depth", which made it more dicult for us to select material for
this chapter. The expansion \in width" has brought in sight new interesting types of modal operators, thus demonstrating again the great expressive power of propositional modal languages. They include, for instance,
polyadic operators, graded modalities, the xed point and di erence operators. We hope the corresponding systems will be considered in detail
elsewhere in the Handbook in this chapter they are briey discussed in the
appendix, where the reader can nd enough references.
Instead of trying to cover the whole variety of existing types of modal
operators, we decided to restrict attention mainly to the classes of normal
(and quasi-normal) uni- and polymodal logics and follow \in depth" the
way taken by Bull and Segerberg in Basic Modal Logic, the more so that
this corresponds to our own scientic interests.
Having gone over from considering individual modal systems to big classes
of them, we are certainly interested in developing general methods suitable
for handling modal logics en masse. This somewhat changes the standard
set of tools for dealing with logics and gives rise to new directions of research.
First, we are almost completely deprived of proof-theoretic methods like
Gentzen-style systems or natural deduction. Although proof theory has
been developed for a number of important modal logics, it can hardly be
extended to reasonably representative families. (Proof theory is discussed
in the chapter Sequent systems for modal logics some references to recent
results can be found in the appendix.)

ADVANCED MODAL LOGIC

3

In fact, modern modal logic is primarily based upon the frame-theoretic
and algebraic approaches. The link connecting syntactical representations
of logics and their semantics is general completeness theory which stems
from the pioneering results of Bull 1966b], Fine 1974c], Sahlqvist 1975],
Goldblatt and Thomason 1974]. Completeness theorems are usually the
rst step in understanding various properties of logics, especially those that
have semantic or algebraic equivalents. A classical example is Maksimova's
1979] investigation of the interpolation property of normal modal logics
containing S4, or decidability results based on completeness with respect to
\good" classes of frames. Completeness theory provides means for axiomatizing logics determined by given frame classes and characterizes those of
them that are modal axiomatic.
Standard families of modal logics are endowed with the lattice structure
induced by the set-theoretic inclusion. This gives rise to another line of
studies in modal logic, addressing questions like \what are co-atoms in the
lattice?" (i.e., what are maximal consistent logics in the family?), \are there
innite ascending chains?" (i.e., are all logics in the family nitely axiomatizable?), etc. From the algebraic standpoint a lattice of logics corresponds
to a lattice of subvarieties of some xed variety of modal algebras, which
opens a way for a fruitful interface with a well-developed eld in universal
algebra.
A striking connection between \geometrical" properties of modal formulas, completeness, axiomatizability and -prime elements in the lattice of
modal logics was discovered by Jankov 1963, 1969], Blok 1978, 1980b]
and Rautenberg 1979]. These observations gave an impetus to a project
of constructing frame-theoretic languages which are able to characterize
the \geometry" and \topology" of frames for modal logics (Zakharyaschev
1984, 1992], Wolter 1996d]) and thereby provide new tools for proving their
properties and clarifying the structure of their lattices.
One more interesting direction of studies, arising only when we deal with
big classes of logics, concerns the algorithmic problem of recognizing properties of (nitely axiomatizable) logics. Having undecidable nitely axiomatizable logics in a given class (Thomason 1975a], Shehtman 1978b]), it
is tempting to conjecture that non-trivial properties of logics in this class
are undecidable. However, unlike Rice's Theorem in recursion theory, some
important properties turn out to be decidable, witness the decidability of
interpolation above S4 (Maksimova 1979]). The machinery for proving the
undecidability of various properties (e.g. Kripke completeness and decidability) was developed in Thomason 1982] and Chagrov 1990b,c].
Thomason 1982] proved the undecidability of Kripke completeness rst
in the class of polymodal logics and then transferred it to that of unimodal
ones. In fact, Thomason's embedding turns out to be an isomorphism from

T

4

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

the lattice of logics with n necessity operators onto an interval in the lattice of unimodal logics, preserving many standard properties (Kracht and
Wolter 1997a]). Such embeddings are interesting not only from the theoretical point of view but can also serve as a vehicle for reducing the study of
one class of logics to another. Perhaps the best known example of such a
reduction is the Godel translation of intuitionistic logic and its extensions
into normal modal logics above S4 (Maksimova and Rybakov 1974], Blok
1976], Esakia 1979a,b]). We will take advantage of this translation to give
a brief survey of results in the eld of superintuitionistic logics which actually were always studied in parallel with modal logics (see also Section 5 in
Intuitionistic Logic).
Listed above are the most important general directions in mathematical modal logic we are going to concentrate on in this chapter. They, of
course, do not cover the whole discipline. Other topics, for instance, modal
systems with quantiers, the relationship between the propositional modal
language and the rst (or higher) order classical language, or proof theory
are considered in other chapters of the Handbook.
It should be emphasized once again that the reader will nd no discussions of particular modal systems in this chapter. Modal logic is presented
here as a mathematical theory analyzing big families of logics and thereby
providing us with powerful methods for handling concrete ones. (In some
cases we illustrate technically complex methods by considering concrete logics for instance Rybakov's 1994] technique of proving the decidability of
the admissibility problem for inference rules is explained only for GL.)

Acknowledgments. First of all, we are indebted to our friend and colleague Marcus Kracht who not only helped us with numerous advices but
also supplied us with some material for this chapter. We are grateful to
Hiroakira Ono and the members of his Logic Group in Japan Advanced
Institute of Science and Technology for the creative and stimulating atmosphere that surrounded the rst two authors during their stay in JAIST,
where the bulk of the chapter was written. Thanks are also due to Johan
van Benthem, Wim Blok, Dov Gabbay, Silvio Ghilardi, Krister Segerberg,
Heinrich Wansing for their helpful comments and stimulating discussions.
And certainly our work would be impossible without constant support and
love of our wives: Olga, Imke and Lilia.
Partly the work of the rst author was nanced by the Alexander von
Humboldt Foundation.

ADVANCED MODAL LOGIC

5

1 UNIMODAL LOGICS
We begin by considering normal modal logics with one necessity operator,
which were introduced in Section 6 of Basic Modal Logic. Recall that each
such logic is a set of modal formulas (in the language with the primitive
connectives ^, _, !, ?, 2) containing all classical tautologies, the modal
axiom 2(p ! q) ! (2p ! 2q), and closed under substitution, modus
ponens and necessitation '=2'.

1.1 The lattice NExtK

First let us have a look at the class of normal modal logics from a purely
syntactic point of view. Given a normal modal logic L0 , we denote by
NExtL0 the family of its normal extensions. NExtK is thus the class of all
normal modal logics. Each logic L in NExtL0 can be obtained by adding
to L0 a set of modal formulas ; and taking the closure under the inference
rules mentioned above in symbols this is denoted by
L = L0  ;:
Formulas in ; are called additional (or extra) axioms of L over L0 . Formulas
' and  are said to be deductively equivalent in NExtL0 if L0  ' = L0  .
For instance, 2p ! p and p ! 3p are deductively equivalent in NExtK,
both axiomatizing T, however (2p ! p) $ (p ! 3p) 62 K. (For more information on the relation between these formulas see Chellas and Segerberg
1994] and Williamson 1994].)
We distinguish between two kinds of derivations from assumptions in a
logic L 2 NExtK. For a formula ' and a set of formulas ;, we write ; `L '
if there is a derivation of ' from formulas in L and ; with the help of only
modus ponens. In this case the standard deduction theorem|;  `L ' i
; `L  ! '|holds. The fact of derivability of ' from ; in L using both
modus ponens and necessitation is denoted by ; `L ' in such a case we
say that ' is globally derivable3 from ; in L. For this kind of derivation
we have the following variant of the deduction theorem which is proved by
induction on the length of derivations in the same manner as for classical
logic.
THEOREM 1.1 (Deduction) For every logic L 2 NExtK, all formulas '
and , and all sets of formulas ;,
;  `L ' i 9m 0 ; `L 2m  ! '
where 2m  = 20  ^ : : : ^ 2m  and 2n  is  prexed by n boxes.
3 This name is motivated by the semantical characterization of ` to be given in
L
Theorem 1.19.

6

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

It is to be noted that in general no upper bound for m can be computed
even for a decidable L (see Theorem 4.2). However, if the formula
tran = 2n p ! 2n+1 p
is in L|such L is called n-transitive|then we can clearly take m = n. In
particular, for every L 2 NExtK4, ;  `L ' i ; `L 2+  ! ', where
2+  =  ^ 2. Moreover, a sort of conversion of this observation holds.
THEOREM 1.2 The following conditions are equivalent for every logic L in
NExtK:
(i) L is n-transitive, for some n < !
(ii) there exists a formula (p q) such that, for any ',  and ;,
;  `L ' i ; `L ( '):
Proof The implication (i) ) (ii) is clear. To prove the converse, observe
rst that (p q) `L (p q) and so (p q) p `L q. By Theorem 1.1, we
then have (p q) `L 2n p ! q, for some n. Let q = 2n+1 p. Then
(p 2n+1 p) `L 2n p ! 2n+1 p. And since p `L 2n+1 p, (p 2n+1 p) 2 L.
Consequently, tran 2 L.
2
Remark: Note also that (i) is equivalent to the algebraic condition: the
variety of modal algebras for L has equationally denable principal congruences. For more information on this and close results consult Blok and
Pigozzi 1982].
The sum L1  L2 and intersection L1 \ L2 of logics L1  L2 2 NExtL0 are
clearly logics in NExtL0 as well. The former can be axiomatized simply by
joining the axioms of L1 and L2 . To axiomatize the latter we require the
following denition. Given two formulas '(p1  : : :  pn ) and (p1  : : :  pm)
(whose variables are in the lists p1  : : :  pn and p1  : : :  pm , respectively),
denote by '_ the formula '(p1  : : :  pn ) _ (pn+1  : : :  pn+m ).
THEOREM 1.3 Let L1 = L0  f'i : i 2 I g and L2 = L0  fj : j 2 J g.
Then
L1 \ L2 = L0  f2m 'i _ 2n j : i 2 I j 2 J m n 0g:
Proof Denote by L the logic in the right-hand side of the equality to be
established and suppose that  2 L1 \ L2 . Then for some m n 0 and some
nite I 0 and J 0 such that all '0i and j0 , for i 2 I 0 , j 2 J 0 , are substitution
instances of some 'i and j , for i0 2 I , j 0 2 J , we have

^
^
2 m ' !2L  2 n  !2L 
0

0



0

i 2I

0

i

0



0

j 2J

0

j

0

ADVANCED MODAL LOGIC

7

^ (2k ' _ 2l ) !  2 L

from which

0

i I j J
kl m n

2 0 2 0
0  +

0

i

j

0

and so  2 L because 2k '0i _ 2l j0 is a substitution instance of 2k 'i _2l j .
Thus, L1 \ L2 L. The converse inclusion is obvious.
2
0

0

Although the sum of logics di ers in general from their union, these two
operations have a few common important properties.
THEOREM 1.4 The operation  is idempotent, commutative, associative
and distributes over \ the operation \ distributes over (innite) sums, i.e.,

L\

M Li = M(L \ Li):
i2I

i2I

It follows that hNExtL0  \i is a complete distributive lattice, with L0
and the inconsistent logic, i.e., the set For of all modal formulas, being its
zero and unit elements, respectively, and the set-theoretic its corresponding lattice order. Note, however, that  does not in general distribute over
innite intersections of logics. For otherwise we would have
(K  :2?) 

\ (K  2n?) = \ (K  :2?  2n?)

1n<!

1n<!

which is a contradiction, since the logic in the left-hand side is consistent
(D, to be more precise), while that in the right-hand side is not.
If we are interested in nding a simple (in one sense or another) syntactic
representation of a logic L 2 NExtL0 , we can distinguish nite, recursive
and independent axiomatizations of L over L0. The former two notions
mean that L = L0  ;, for some nite or, respectively, recursive ;, and
a set of axioms ; is independent over L0 if L 6= L0  for any proper
subset of ;. In the case when L0 is K or any other nitely axiomatizable
over K logic, we may omit mentioning L0 and say simply that L is nitely
(recursively, independently) axiomatizable.
It is fairly easy to see that L is not nitely axiomatizable over L0 i
there is an innite sequence of logics L1  L2  : : : in NExtL0 such that
L = i>0 Li . This observation is known as Tarski's criterion. (It is worth
noting that nite axiomatizability is not preserved under \. For example,
using Tarski's criterion, one can show that D \ (K  2p _ 2:p) is not
nitely axiomatizable.) The recursive axiomatizability of a logic L, as was
observed by Craig 1953], is equivalent to the recursive enumerability of L.
As for independent axiomatizability, an interesting necessary condition can
be derived from Kleyman 1984]. Suppose a normal modal logic L1 has an

L

8

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

independent axiomatization. Then, for every nitely axiomatizable normal
modal logic L2  L1, the interval of logics
L2  L1] = fL 2 NExtK : L2 L L1 g
contains an immediate predecessor of L1 . Using this condition Chagrov and
Zakharyaschev 1995a] constructed various logics in NExtK4, NExtS4 and
NExtGrz without independent axiomatizations.
To understand the structure of the lattice NExtL0 it may be useful to
look for a set ; of formulas which is complete in the sense that its formulas
are able to axiomatize all logics in the class, and independent in the sense
that it contains no complete proper subsets. Such a set (if it exists) may be
called an axiomatic basis of NExtL0 . The existence of an axiomatic basis
depends on whether every logic in the class can be represented as the sum
of \indecomposable" logics. A logic L 2 NExtL0 is said to be {irreducible
in NExtL0 if for any family fLi : i 2 I g of logics in NExtL0, L = i2I Li
implies L = Li for some i 2 I . L is {prime if for any family fLi : i 2 I g,
L
i2I Li only if there is i 2 I such that L Li . It is not hard to
see (using Theorem 1.4) that a logic is {irreducible i it is {prime.
This does not hold, however, for the dual notions of {irreducible and {
prime logics. We have only one implication in general: if L is {prime (i.e.,
i2I Li L only if Li L, for some i 2 I ) then it is {irreducible (i.e.,
L = i2I Li only if L = Li , for some i 2 I ). A formula ' is said to be
prime in NExtL0 if L0  ' is {prime in NExtL0.
PROPOSITION 1.5 Suppose a set of formulas ; is complete for NExtL0
and contains no distinct deductively equivalent in NExtL0 formulas. Then
; is an axiomatic basis for NExtL0 i every formula in ; is prime.
Although the denitions above seem to be quite simple, in practice it
is not so easy to understand whether a given logic is { or {prime, at
least at the syntactical level. However, these notions turn out to be closely
related to the following lattice-theoretic concept of splitting for which in the
next section we shall provide a semantic characterization.
A pair (L1  L2 ) of logics in NExtL0 is called a splitting pair in NExtL0
if it divides the lattice NExtL0 into two disjoint parts: the lter NExtL2
and the ideal L0  L1]. In this case we also say that L1 splits and L2 cosplits
NExtL0 .
THEOREM 1.6 A logic L1 splits NExtL0 i it is {prime in NExtL0 , and
L2 cosplits NExtL0 i it is {prime in NExtL0 . Moreover, the following
conditions are equivalent:
(i) (L1  L2 ) is a splitting pair in NExtL0
(ii) L1 is {prime in NExtL0 and L2 = fL 2 NExtL0 : L 6 L1 g
(iii) L2 is {prime in NExtL0 and L1 = fL 2 NExtL0 : L 6 L2 g.

L

L

T

T

L

L

T

L

T

T

L T

T

L

T
L

T
L

L

L

T

ADVANCED MODAL LOGIC

9

Splittings were rst introduced in lattice theory by Whitman 1943] and
McKenzie 1972] (see also Day 1977], Jipsen and Rose 1993]). Jankov
1963, 1968b, 1969], Blok 1976] and Rautenberg 1977] started using splittings in non-classical logic.
A few standard normal modal logics are listed in Table 1. Note that
our notations are somewhat di erent from those used in Basic Modal logic.
(A was introduced by Artemov see Shavrukov 1991]. The formulas Bn
bounding depth of frames are dened in Section 15 of Basic Modal Logic.)

1.2 Semantics

The algebraic counterpart of a logic L 2 NExtK is the variety of modal
algebras validating L (for denitions consult Section 10 of Basic Modal
Logic). Conversely, each variety (equationally denable class) V of modal
algebras determines the normal modal logic LogV = f' : 8A 2 V A j= 'g.
Thus we arrive at a dual isomorphism between the lattice NExtK and the
lattice of varieties of modal algebras, which makes it possible to exploit the
apparatus of universal algebra for studying modal logics.
It is often more convenient, however, to deal not with modal algebras
directly but with their relational representations discovered by Jonsson and
Tarski 1951] and now known as general frames. Each general frame F =
hW R P i is a hybrid of the usual Kripke frame hW Ri and the modal algebra
F+ = hP  W ; \  2 3i in which the operations 2 and 3 are uniquely
determined by the accessibility relation R: for every X 2 P 2W ,

2X = fx 2 W : 8y (xRy ! y 2 X )g 3X = ;2 ; X:
So, using general frames we can take advantage of both relational and algebraic semantics. To simplify notation, we denote general frames of the form
F = W R 2W by F = hW Ri. Such frames will be called Kripke frames.
Given a class of frames C , we write LogC to denote the logic determined by
C , i.e., the set of formulas that are valid in all frames in C  it is called the
logic of C . If C consists of a single frame F, we write simply LogF.
Basic facts about duality between frames and algebras can be found in the
chapters Basic Modal Logic and Correspondence Theory. Here we remind
the reader of the denitions that will be important in what follows.
A frame G = hV S Qi is said to be a generated subframe of a frame
F = hW R P i if V W is upward closed in F, i.e., x 2 V and xRy imply
y 2 V , S = R V and Q = fX \ V : X 2 P g. The smallest generated
subframe G of F containing a set X W is called the subframe generated
by X . A frame F is rooted if there is x 2 W |a root of F|such that the
subframe of F generated by fxg is F itself.





10

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

D
T
KB
K4
K5
Altn
D4
S4
GL
Grz
K4:1
K4:2
K4:3
S4:1
S4:2
S4:3
Triv
Verum
S5
K4B
A
Dum
K4BWn
K4BDn
K4nm

=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=

K  2p ! 3p
K  2p ! p
K  p ! 23p
K  2p ! 22p
K  32p ! 2p
K  2p1 _ 2(p1 ! p2) _ : : : _ 2(p1 ^ : : : ^ pn ! pn+1)
K4  3>
K4  2p ! p
K4  2(2p ! p) ! 2p
K  2(2(p ! 2p) ! p) ! p
K4  23p ! 32p
K4  3(p ^ 2q) ! 2(p _ 3q)
K4  2(2+ p ! q) _ 2(2+ q ! p)
S4  23p ! 32p
S4  32p ! 23p
S4  2(2p ! q) _ 2(2q ! p)
K4  2p $ p
K4  2p
S4  p ! 23p
K4  p ! 23p
GL  22p ! 2(2+ p ! q) _ 2(2+ q ! p)
S4  2V(2(p ! 2p)W! p) ! (32p ! p)
K4  ni=0 3pi ! 0i6=jn 3(pi ^ (pj _ 3pj ))
K4  Bn
K4  2n p ! 2mp for 1  m < n

Table 1. A list of standard normal modal logics.

ADVANCED MODAL LOGIC

11

A map f from W onto V is a reduction (or p-morphism) of a frame
F = hW R P i to G = hV S Qi if the following three conditions are satised
for all x y 2 W and X 2 Q
(R1)
xRy implies f (x)Sf (y)
(R2)
f (x)Sf (y) implies 9z 2 W (xRz ^ f (z ) = f (y))
(R3)
f ;1 (X ) 2 P .
The operations of reduction and generating subframes are relational counterparts of the algebraic operations of forming subalgebras and homomorphic images, respectively, and so preserve validity.
A frame F = hW R P i is dierentiated if, for any x y 2 W ,
x = y i 8X 2 P (x 2 X $ y 2 X ):
F is tight if
xRy i 8X 2 P (x 2 2X ! y 2 X ):
Those frames that are both di erentiated and tight are called rened. A
frame F is said to be compactTif every subset X of P with the nite intersection property (i.e., with X 0 =
6  for any nite subset X 0 of X ) has
non-empty intersection. Finally, rened and compact frames are called descriptive. A characteristic property of a descriptive F is that it is isomorphic
to its bidual (F+ )+ . The classes of all di erentiated, tight, rened and descriptive frames will be denoted by DF , T , R and D, respectively.
When representing frames in the form of diagrams,
we denote by  ir
reexive points, by  reexive ones, and by  two-point clusters. An arrow
from x to y means that y is accessible from x. If the accessibility relation
is transitive, we draw arrows only to the immediate successors of x.
EXAMPLE 1.7 (Van Benthem 1979) Let F = hW R P i be the frame whose
underlying Kripke frame is shown in Fig. 1 (! + 1 sees only ! and the
subframe generated by ! is transitive) and X W is in P i either X is
nite and ! 2= X or X is conite in W and ! 2 X . It is easy to see that
P is closed under \, ; and 3. Clearly, F is rened. Suppose X is a subset
of P with Tthe nite intersection property. If X contains a nite set Tthen
obviously X =
6 . And if X consists of only innite sets then ! 2 X .
Thus, F is descriptive.
A frame F is said to be {-generated, { a cardinal, if its dual F+ is
a {-generated algebra.4 Each modal logic L is determined by the free
nitely generated algebras in the corresponding variety, i.e., by the Tarski{
Lindenbaum (or canonical) algebras AL(n) for L in the language with n <
4 An algebra is said to be { -generated if it contains a set X of cardinality  { such
that the closure of X under the algebra's operations coincides with its universe.

12

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

nontransitive

transitive

! + 1-!   2 -1 -0
Figure 1.

! variables. Their duals are denoted by FL(n) = hWL (n) RL (n) PL (n)i
and called the universal frames of rank n for L. Analogous notation and
terminology will be used for the free algebras AL({) with { generators.
Note that hWL ({) RL ({)i is (isomorphic to) the canonical Kripke frame
for L with { variables (dened in Section 11 of Basic Modal Logic) and
PL ({) is the collection of the truth-sets of formulas in the corresponding

canonical model. Unless otherwise stated, we will assume in what follows
that the language of the logics under consideration contains ! variables.
An important property of the universal frame of rank { for L is that
every descriptive {0 -generated frame for L, {0  {, is a generated subframe
of FL ({). Thus, the more information about universal frames for L we have,
the deeper our knowledge about the structure of arbitrary frames for L and
thereby about L itself.
Although in general universal frames for modal logics are very complicated, considerable progress was made in clarifying the structure of the
upper part (points of nite depth) of the universal frames of nite rank
for logics in NExtK4. The studies in this direction were started actually
by Segerberg 1971]. Shehtman 1978a] presented a general method of constructing the universal frames of nite rank for logics in NExtS4 with the
nite model property. Later similar results were obtained by other authors
see e.g. Bellissima 1985]. The structure of free nitely generated algebras
for S4 was investigated by Blok 1976].
Let us try to understand rst the constitution of an arbitrary transitive
rened frame F = hW R P i with n generators G1  : : :  Gn 2 P . Dene V
to be the valuation of the set of variables # = fp1 : : :  pn g in F such that
x j= pi i x 2 Gi . Say that points x and y are #-equivalent, x  y in
symbols, if the same variables in # are true at them for X Y W we
write X  Y if every point in X is #-equivalent to some point in Y and
vice versa. Let d(F) denote the depth5 of F if F is of innite depth, we
write d(F) = 1. For d < d(F), W =d and W >d are the sets of all points in F
of depth d and > d, respectively W <d , W d, etc. are dened analogously.
Fd is the subframe of F generated by W d . The set of all successors
(predecessors) of points in a set X W is denoted by X " (respectively,
5

In Section 15 of Basic Modal Logic d(F) was called the rank of F.

ADVANCED MODAL LOGIC

13

X #) in the transitive case X " = X "  X and X # = X #  X are then the
upward and downward closure operations. A set X is said to be a cover for
a set Y in F if Y X #. A point x is called an atom in F if fxg 2 P .
THEOREM 1.8 Suppose F = hW R P i is a transitive rened n-generated
frame, for some n < !. Then
(i) each cluster in F contains  2n points
(ii) for every nite d  d(F), W =d is a cover for W d and contains at
most cn (d) distinct clusters, where
cn (1) = 2n + 22n ; 1 cn (m + 1) = cn (1)  2cn(1)+:::+cn (m) 
(iii) every point of nite depth in F is an atom.
Proof (i) follows from the di erentiatedness of F and the obvious fact that
precisely the same formulas (in p1  : : :  pn ) are true under V at #-equivalent
points in the same cluster.
The proof of (ii) proceeds by induction on d. Let x 2 W >d. Since F is
transitive and W d is nite (by the induction hypothesis), there exists a
non-empty upward closed in W >d set X (i.e., X = X " \ W >d) such that
x 2 X #, points in X see exactly the same points of depth  d and either
8u v 2 X 9w 2 u" \ X w  v
(1)

or

8u v 2 X (u  v ^ :uRv):
(2)
Such a set X is called d-cyclic it is nondegenerate if (1) holds and degenerate
otherwise. One can readily show that the same formulas are true at #equivalent points in X . Since F is rened, X is then a cluster of depth
d + 1. Thus, W >d W =d+1 #. The upper bound for the number of distinct
clusters of depth d + 1 follows from the di erentiatedness of F and the
denition of d-cyclic sets.
To establish (iii), for every point x of depth d + 1 one can construct
by induction on d a formula (expressing the denition of the d-cyclic set
containing x) which is true in F under V only at x. For details consult
Chagrov and Zakharyaschev 1997].
2

It is fairly easy now to construct the (generated) subframe F<K41 (n) of the
universal frame of rank n for K4 consisting of nite depth points. Indeed,
FK4 (n) is n-generated, rened and so has the form as described in Theorem 1.8. On the other hand, it is universal and contains any n-generated
descriptive frame as a generated subframe, which means roughly that it contains all possible points of nite depth that can exist in n-generated rened
frames.

14

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

p1

FS42 (1)

P
H
~
a
PP
a
Q
P
bH

P
Q
c
c
# AC
aP
bH
P
;
Q
Q
PP ##


C
S
@
;

S
@

A
c

#

a
c

b
;
aP
 CAS@Q
P
 S@Q

  CA
c P
#;
P
a
cH
#
bH
P
P
a
P
a
  C AS@Q
P
PPS@Q
bHH 
;  C A
cQ
#
c
# ;
Q
bH
P
;Q
@P
CA
aP
cQ

C A S@
#c
   aP
SP
P
;  
b #H
a
P
Q
P
P
#;
a
c
b H 
@
P
C A
 
C A#S;@
cQ

S
a
P
Q
Q

P
b
c Q
#a
H H
P
a
c
#
P

;
A

@
P
C
Q
 
C

S
@

S
;
P
b
c
P
caP
#
HHC AA
b
QP
 # a
PP
A S @
P
 
C 
 cQ
b
# ;
PP
Q
Q # S;@ caa
P
H
P
P
C HA
Qbb
 ~ # ~; C A~ S @c~#Q; S @~ c a
~P

p1

p1

p1

p1

p1

Figure 2.
More precisely, assuming that each point is assigned the set of variables
in # that are true at it, we begin constructing a frame GK4 (n) nby putting
at depth 1 in it 2n non-#-equivalent degenerate clusters and 22 ; 1 non#-equivalent non-degenerate clusters with  2n non-#-equivalent points.
Suppose that GK4d (n) is already constructed. Then for every antichain a of
clusters in GK4d (n) containing at least one cluster of depth d and di erent
from a singleton
with a non-degenerate cluster, we add to GK4d (n) copies
n
n
2
of all 2 + 2 ; 1 clusters of depth 1 so that they would be inaccessible
from each other and could see only the clusters in a and their successors.
And for every singleton a = fC g with a non-degenerate cluster C , we add
to GK4d (n) copies of those clusters of depth 1 which are not #-equivalent to
any subset of C (otherwise the frame will not be rened) so that again they
would be mutually inaccessible and could see only C and its successors in
GK4d (n).
Let NK4 (n) = hGK4 (n) UK4 (n)i be the resulting model (the relational
component of GK4 (n) is completely determined by the construction and its
set of possible values is the collection of the truth-sets of formulas in GK4 (n)
under UK4 (n)). It is not hard to show that GK4 (n) is atomic. Moreover, for
every point x in this frame one can construct a formula '(p1  : : :  pn ) such
that x 6j= ' and, for any frame F, F 6j= ' i there is a generated subframe of F
reducible to the subframe of GK4 (n) generated by x. It follows in particular
that GK4 (n) is rened. Thus, every GK4d (n) is a generated subframe of
FK4 (n). On the other hand, by Theorem 1.8, FK4 (n) contains no clusters
of depth  d di erent from those in GK4d (n) and so F<K41 (n) is isomorphic to
GK4 (n). It worth noting also that, since K4 has the nite model property,
it is characterized by F<K41 (n), and so FK4 (n) is isomorphic to the bidual of
F<K41 (n).
The universal frame FL(n) for an arbitrary consistent logic L in NExtK4
is a generated subframe of FK4 (n). It can be constructed by removing

ADVANCED MODAL LOGIC

15

from FK4 (n) those points at which some formulas in L are refuted (under
VK4 (n)). For example, F<S41(n) is obtained by removing from F<K41 (n)
all irreexive points and their predecessors. In other words, F<S41 (n) can
be constructed in the same way as F<K41 (n) but using only non-degenerate
clusters. FS42 (1) (the corresponding model, to be more exact) is shown in
Fig. 2, where ~ denotes the cluster with two points at one of which p1 is
1 (n) and F<1 (n), we take only simple clusters and
true. To construct F<Grz
GL
degenerate clusters, respectively.
In general, this method of constructing universal frames does not work
for logics with nontransitive frames. However, using the fact that K is
characterized by the class of nite intransitive irreexive trees (see Section
13 of Basic Modal Logic), in the same manner as above one can construct
an intransitive irreexive model characterizing K and such that FK (n) is
isomorphic to the bidual of the frame associated with this model.
Let us consider now the semantical meaning of splittings. In view of the
following observation we focus attention only on splittings by the logics of
nite rooted frames.
THEOREM 1.9 If L1 splits NExtL0 and L0 has the nite model property
then L1 = LogF, for some nite rooted frame F validating L0.
Proof Since L2 in the splitting pair (L1 L2) is a proper extension of L0,
there is a nite frame G such that G j= L0 and G 6j= L2 . It follows that
LogG L1 . As we shall see later (Corollary 1.86), every extension of a
tabular logic is also tabular. So L1 = LogF for some nite F j= L0. And
since L1 is {prime, F must be rooted.
2
We say that a frame F splits NExtL0 if LogF splits NExtL0. The logic L2
of the splitting pair (LogF L2 ) is denoted by L0 =F and called the splitting
of NExtL0 by F. This notation reects the fact that L2 is the smallest logic
in NExtL0 which is not validated by F.
EXAMPLE 1.10 We show that D = K=. Recall that D = K  3> is
characterized by the class of serial frames (in which every point has a successor). So if  j= L then L Log otherwise no frame for L has a dead
end, which means that 3> 2 L and D L. The inconsistent logic For can
be represented as D=.
To illustrate some applications of splittings we require a few denitions.
Given L 2 NExtL0 , we say that the axiomatization problem for L above
L0 is decidable if the set f' : L0  ' = Lg is recursive. L is strictly
Kripke complete above L0 if no other logic in NExtL0 has exactly the same
Kripke frames as L. If all frames in a set F split NExtL0, we call the logic
fL0 =F : F 2 Fg the union-splitting of NExtL0 and denote it by L0 =F .

T

L

16

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

EXAMPLE 1.11 Grz is not a splitting of NExtS4. However, it is a union
6


splitting: Grz = S4=f   g. S4:1 = S4= . A frame may split the
lattice NExtL0=F but not NExtL0 : e.g.  splits NExtK= but does not
split NExtK.
THEOREM 1.12 Suppose L 2 NExtL0 and L = (: : : (L0 =F1 )= : : :)=Fn , for
a sequence F1  : : :  Fn of sets of nite rooted frames.
(i) If F = ni=1 Fi is nite and L is decidable then the axiomatization
problem for L above L0 is decidable. More precisely,
f' : L0  ' = Lg = f' 2 L : 8F 2 F F 6j= 'g:
(ii) If L is Kripke complete then L is strictly Kripke complete above L0 .
(iii) The immediate predecessors of L in NExtL0 are precisely the logics
L \ LogF, for F 2 F such that F is not a reduct of a generated subframe of
another frame in F .
Proof (i) is left to the reader as an easy exercise.
(ii) Let L0 be a logic in NExtL0 with the same Kripke frames as L. Then
obviously L0 L. On the other hand, the frames in F do not validate L0
and so L L0.
(iii) If L0 is an immediate predecessor of L in NExtL0 then F j= L0 , for
some F 2 F . Therefore, L0 L \ LogF  L and so L0 = L \ LogF. Suppose
now that F is not a reduct of a generated subframe of another frame in F
and L \ LogF L0  L. Then L0 LogF0 for some F0 2 F , and hence
F0 = F, L0 = L \ LogF.
2
As follows from Theorem 1.12 and Example 1.10, For has exactly two
immediate predecessors Verum = Log and Triv = Log (and each consistent normal modal logic is contained in one of them). This result is known
as Makinson's 1971] Theorem. Moreover, the axiomatization problem for
For is decidable, i.e., there is an algorithm which decides, given a formula
' whether K  ' is consistent. Likewise, since D = K  3> is decidable,
there is an algorithm recognizing, given ', whether D = K  '. We shall
see later in Section 4.4 that in fact not so many properties of logics are
decidable (e.g. the axiomatization problem for K  :3> is undecidable
see Theorem 4.15) and that Theorem 1.12 (i) provides the main method for
proving decidability results of this type.
To determine whether a nite rooted frame F = hW Ri splits NExtL0,
we need the formulas dened below:
F = fpx ! 3py : x y 2 W xRyg 
fpx ! :3py : x y 2 W :xRyg 
fpx ! :py : x y 2 W x 6= yg

S

ADVANCED MODAL LOGIC

^

_

17

F=
F  F = F ^ fpx : x 2 W g:
The meaning of F is explained by the following lemma, in which

2<! ' = f2n ' : n < !g:
LEMMA 1.13 For any nite F with root r, the set of formulas fpr g 2<! F
is satisable in a frame G i there is a generated subframe H of G reducible
to F. Moreover, if F is cycle free (i.e., contains no path from a point to
itself) then ! can be replaced by n = d(F) + 1.

Proof ()) Suppose fpr g  2<! F is satised at a point u in G. It is not

hard to check that the map f dened by f (v) = x i v j= px is a reduction of
the subframe H of G generated by u to F. If F is cycle free and fpr g 2<! F
is satised at u then d(H) = d(F). For otherwise an ascending chain of n +1
points starts from u and so F must contain a cycle.
(() Let f be a reduction of H to F. Dene a valuation in G so that
v j= px i v 2 f ;1 (x). The reader can readily verify that under this
valuation fpr g  2<! F is true at any point in f ;1 (r).
2
LEMMA 1.14 For every logic L 2 NExtK and every nite rooted frame F,
F j= L i 8n < ! 2n F ! :pr 62 L.

Proof The implication ()) follows from Lemma 1.13. Suppose now that

2n F ! :pr 62 L, for every n < !. Then the set fpr g  2<! F is Lconsistent and so it is satised in a frame G for L. By Lemma 1.13, a
generated subframe of G is reducible to F, and hence F j= L.
2
We are now in a position to characterize nite frames that split NExtL0

and to axiomatize splittings.

THEOREM 1.15 Suppose F is a nite frame with root r and L0 2 NExtK.
Then F splits NExtL0 i there is n < ! such that, for every frame G j= L0 ,
2n F ^ pr is satisable in G only if 2m F ^ pr is satisable in G for every
m > n. In this case L0 =F = L0  2n F ! :pr .

Proof ()) Suppose otherwise and consider a sequence fGn : n < !g of

frames for L0 such that 2n F ^ pr is satisable in Gn but 2m F ^ pr is
not satised, for some m > n. By Lemma 1.14, the former condition implies
n<! LogGn LogF, while the latter means that F 6j= LogGn , for every
n < !, contrary to LogF being {prime.
(() We show that L0 =F = L0  2n F ! :pr . Suppose L 6 LogF.
Then, by Lemma 1.14, there is m < ! such that 2m F ! :pr 2 L. It
follows that 2n F ! :pr 2 L and so L0  2n F ! :pr L.
2

T

T

18

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

For more general versions of this criterion consult Kracht 1990] and
Wolter 1993].
COROLLARY 1.16 (Rautenberg 1980) Suppose that L0 2 NExt(Ktran ),
for some n < !. Then every nite rooted frame F for L0 splits NExtL0 and
L0 =F = L0  2n F ! :pr .
In particular, every transitive nite rooted frame splits NExtK4. This
result may also be obtained using the fact that all nite subdirectly irreducible algebras split the lattice of subvarieties of a variety with equationally
denable principal congruences (see Blok and Pigozzi 1982]). However, not
every frame splits NExtK.
THEOREM 1.17 (Blok 1978) A nite rooted frame F splits NExtK i it is
cycle free. In this case K=F = K  2n F ! :pr , where n = d(F).

Proof That frames with cycles do not split NExtK follows from the fact
that K is characterized by cycle free nite rooted frames. And the converse
is an immediate consequence of Lemma 1.13 and Theorem 1.15.

2

An element x 6= 0 of a complete lattice L is called an atom in L if the zero
element 0 in L is the immediate predecessor of x, i.e., there is no y such that
0 < y < x. Splittings turn out to be closely related to the existence of atoms
in nitely generated free algebras see Blok 1976], Bellissima 1984, 1991]
and Wolter 1997c]. We demonstrate the use of splittings by the following
THEOREM 1.18 (Blok 1980a) The lattice NExtK has no atoms.

Proof If a logic L is an atom in NExtK, it is L{prime. It follows that
L cosplits NExtK and the logic L0 = LogF in the splitting pair (L0  L)
has no proper predecessor that splits NExtK. Add a new irreexive root
to F. By Theorem 1.17, the resulting frame G splits NExtK, and clearly
LogG  LogF, which is a contradiction.

2

A logic is linked with its semantics via completeness theorems. The most
general completeness theorem states that every consistent normal modal
logic is characterized by the class of (descriptive) frames validating it. Or,
if we want to characterize the consequence relations `L and `L, we can use
the following
THEOREM 1.19 (i) For L 2 NExtK, ; `L ' i for any model M based on
a frame for L and any point x in M, x j= ; implies x j= '.
(ii) For L 2 NExtK, ; `L ' i for any model M based on a frame for
L, M j= ; implies M j= '.

ADVANCED MODAL LOGIC

19

However, usually more specic completeness results are required. What
is the \geometry" of frames for a given logic? Are Kripke or even nite
frames enough to characterize it? Questions of this sort will be addressed
in the next several sections.

1.3 Persistence
The structure of Kripke frames for many standard modal logics can be
described by rather simple conditions on the accessibility relation which
are expressed in the rst order language with equality and a binary (accessibility) predicate R. (This observation was actually the starting point
of investigations in Correspondence Theory studying the relation between
modal and rst (or higher) order languages see Chapter 4 of this volume.)
Moreover, in many cases it turns out that the universal frame FL(!) for such
a logic L also satises the corresponding rst order condition . Since says
nothing about sets of possible values in PL (!), it follows immediately that
the canonical (Kripke) frame FL (!) also satises and so characterizes
L. Thus we obtain a completeness theorem of the form:

' 2 L i F j= ' for every Kripke frame F satisfying .
This method of establishing Kripke completeness, known as the method
of canonical models, is based essentially upon two facts: rst, that L is
characterized by its universal frame FL(!) and second, that L is \persistent"
under the transition from FL(!) to its underlying Kripke frame. Of course,
instead of FL(!) we can take any other class of frames C with respect to
which L is complete and try to show that L is C {persistent in the sense
that, for every F = hW R P i in C , if F j= L then F = hW Ri validates L
as well.
PROPOSITION 1.20 If a logic is both C {complete and C {persistent, then it
is complete with respect to the class f F : F 2 Cg of Kripke frames.
It follows in particular that L is Kripke complete whenever it is DF {,
or R{, or D{persistent. Since every descriptive frame for L is a generated
subframe of a suitable universal frame for L, L is D{persistent i it is
persistent with respect to the class of its universal frames. It is an open
problem, however, whether canonicity, i.e., FL (!){persistence, implies D{
persistence. Here are two simple examples.
THEOREM 1.21 (van Benthem 1983) A logic is persistent with respect to
the class of all general frames i it is axiomatizable by a set of variable free
formulas.

20

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

It is easily checked that a Kripke frame validates Altn i no point in it
has more than n distinct successors (see Segerberg 1971]).
THEOREM 1.22 (Bellissima 1988) Every L 2 NExtAltn is DF {persistent,
for any n < !.
Proof The proof is based on the fact that, for any di erentiated frame
F = hW R P i, any nite X W , and any y 2 X , there is Y 2 P such
that X \ Y = fyg. It follows that at most n distinct points are accessible
from every point in a di erentiated frame for L in particular, Altn is DF {
persistent. Suppose now that a formula ' 2 L is refuted at a point x under a
valuation V in F, F a di erentiated frame for L. Let X be the set of points
accessible from x in  md(') steps.6 Since X is nite, there is a valuation
U in F such that U(p) \ X = V(p), for every variable p. Consequently, ' is
false in F at x under U, which is a contradiction.
2
The proof of Fine's 1974c] Theorem that all logics of nite width, i.e.,
logics in NExtK4BWn , for n < !, are Kripke complete (a sketch can be
found in Section 18 of Basic Modal Logic) may also be regarded as a proof
of persistence. Recall that a point x in a transitive frame F = hW R P i
is called non-eliminable (relative to R) if there is X 2 P such that x 2 X
but no proper successor of x is in X (in other words, x is maximal in
X ) in this case we write x 2 maxR X . Denote by Wr the set of all noneliminable points in F and put Fr = hWr  Rr  Pr i, where Rr = R Wr ,
Pr = fX \ Wr : X 2 P g. (Fine called the frame Fr reduced.)
THEOREM 1.23 (Fine 1985) Let F = hW R P i be a transitive descriptive
frame and x 2 X 2 P . Then (i) there exists a point y 2 maxR X \ x" and
(ii) Fr is a rened frame whose dual F+r is isomorphic to F+ .
Proof (i) Suppose otherwise, i.e., there is no maximal point in X \ x".
Let Y be a maximal chain of points in X \ x" (that it exists follows from
Zorn's Lemma) and X = fZ 2 P : 9y 2 Y y " \ Y Z g. Clearly, X is
non-empty and has the nite intersection property (because X \ x" has no
maximal point). By compactness, we then have a point z in X which, by
tightness, is maximal in Y , contrary to X \ x" having no maximal point.
(ii) is a consequence of (i).
2
It follows that to establish the Kripke completeness of a logic L 2 NExtK4
it is enough to show that it is persistent with respect to the class
RE = fFr : F a nitely generated descriptive frameg:
That is what Fine 1974c] actually did for logics of nite width.

T

6 Here md('), the modal degree of ', is the length of the longest chain of nested modal
operators in '.

ADVANCED MODAL LOGIC

21

THEOREM 1.24 (Fine 1974c) All logics of nite width are RE {persistent
and so Kripke complete.
Let us return, however, to the method of canonical models. Having tried
it for a number of standard systems, Lemmon and Scott 1977] found a
rather general sucient condition for its applicability and put forward a
conjecture concerning a further extension (which was proved by Goldblatt
1976b]). This direction of completeness (and correspondence) theory culminated in the theorem of Sahlqvist 1975] who proved an optimal (in a sense)
generalization of the condition of Lemmon and Scott 1977]. To formulate it
we require the following denition. Say that a formula is positive (negative )
if it is constructed from variables (negated variables) and the constants >,
? using ^, _, 3 and 2.
THEOREM 1.25 (Sahlqvist 1975) Suppose ' is a formula which is equivalent in K to a formula of the form 2k ( ! ), where k 0,  is positive
and  is constructed from variables and their negations, ? and > with the
help of ^, _, 2 and 3 in such a way that no 's subformula of the form
1 _ 2 or 31, containing an occurrence of a variable without :, is in the
scope of some 2. Then one can eectively construct a rst order formula
(x) in R and = having x as its only free variable and such that, for every
descriptive or Kripke frame F and every point a in F,
(F a) j= ' i F j= (x)a]:
(Here (F a) j= ' means that ' is true at a in F under any valuation.)

Proof We present a sketch of the proof found by Sambin and Vaccaro

1989]. Given a formula '(p1  : : :  pn ), a frame F = hW R P i and sets
X1  : : :  Xn 2 P , denote by '(X1  : : :  Xn ) the set of points in F at which '
is true under the valuation V dened by V(pi ) = Xi , i.e., '(X1  : : :  Xn ) =
V('). Using this notation, we can say that
(F x) j= '(p1  : : :  pn ) i 8X1 : : :  Xn 2 P x 2 '(X1  : : :  Xn ):
EXAMPLE 1.26 Let us consider the formula 2p ! p and try to extract
a rst order equivalent for it in the class of tight frames directly from the
equivalence above and the condition of tightness. For every tight frame
F = hW R P i we have:
(F x) j= 2p ! p i
i
i

8X 2 P x 2 (2X ! X )
8X 2 P (x 2 2X ! x 2 X )
8X 2 P (x" X ! x 2 X ):

22

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

To eliminate the variable X ranging over P , we can use two simple observations. The rst one is purely set-theoretic:
8X 2 P (Y X ! x 2 X ) i x 2 fX 2 P : Y X g:
(3)
And the second one is just a reformulation of the characteristic property of
tight frames:
fX 2 P : x" X g = x":
(4)
With the help of (3) and (4) we can continue the chain of equivalences above
with two more lines:
(F x) j= 2p ! p i : : :
i x 2 fX 2 P : x" X g
i x 2 x":
Thus, F j= 2p ! p i 8x x 2 x" i 8x xRx.
The proof of Sahlqvist's Theorem is a (by no means trivial) generalization
of this argument. Dene by induction x"0 = fxg, x"n+1 = (x"n )", and notice
that in (4) we can replace x" by any term of the form x1"n1  : : :  xk"nk ,
thus obtaining the equality
fX 2 P : x1"n1  : : :  xk"nk X g = x1"n1  : : :  xk"nk
(5)

\

\

T

\

which holds for every tight frame F = hW R P i, all x1  : : :  xk 2 W and all
n1  : : :  nk 0.
A frame-theoretic term x1"n1  : : :  xk"nk with (not necessarily distinct)
world variables x1  : : :  xk will be called an R-term. It is not hard to see
that for any R-term T , the relation x 2 T on F = hW R P i is rst order
expressible in R and =. Consequently, we obtain
LEMMA 1.27 Suppose '(p1  : : :  pn ) is a modal formula and T1 : : :  Tn are
R-terms. Then the relation x 2 '(T1  : : :  Tn ) is expressible by a rst order
formula (in R and =) having x as its only free variable.
Syntactically, R-terms with a single world variable correspond to modal
formulas of the form 2m1 p1 ^ : : : ^ 2mk pk with not necessarily distinct
propositional variables p1  : : :  pk . Such formulas are called strongly positive.
By induction on the construction of ', one can prove the following
LEMMA 1.28 Suppose '(p1  : : :  pn ) is a strongly positive formula containing all the variables p1  : : :  pn and F = hW R P i is a frame. Then one
can eectively construct R-terms T1  : : :  Tn (of one variable x) such that
for any x 2 W and any X1  : : :  Xn 2 P ,
x 2 '(X1  : : :  Xn ) i T1 X1 ^ : : : ^ Tn Xn :

ADVANCED MODAL LOGIC

23

Now, trying to extend the method of Example 1.26 to a wider class of
formulas, we see that it still works if we replace the antecedent 2p in 2p ! p
with an arbitrary strongly positive formula . As to generalizations of the
consequent, let us take rst an arbitrary formula  instead of p and see
what properties it should satisfy to be handled by our method.
Thus, for a modal formula ( ! )(p1  : : :  pn ) with strongly positive 
and a tight frame F = hW R P i, we have:
(F x) j=  !  i 8X1 : : :  Xn 2 P (x 2 (X1  : : :  Xn ) !
x 2 (X1  : : :  Xn ))
i 8X1 : : :  Xn 2 P (T1 X1 ^ : : : ^ Tn Xn !
x 2 (X1  : : :  Xn ))
i 8X1 : : :  Xn;1 2 P (T1 X1 ^ : : : ^ Tn;1 Xn;1 !
8Xn 2 P (Tn Xn ! x 2 (X1  : : :  Xn ))):
(3) does not help us here, but we can readily generalize it to
8X 2 P (Y X ! x 2 (: : :  X : : :)) i
x 2 f(: : :  X : : :) : Y X 2 P g:
(6)

\

So
(F x) j=  !  i 8X1 : : :  Xn;1 2 P (T1 X1 ^ : : : ^ Tn;1 Xn;1 !
x 2 f(X1  : : :  Xn ) : Tn Xn 2 P g):

\

But now (4) and (5) are useless. In fact, what we need is the equality

\f(: : :  X : : :) : T X 2 P g =
\
(: : :  fX 2 P : T X g : : :)

(7)

which, with the help of (5), would give us

\f(: : :  X : : :) : T X 2 P g = (: : :  T : : :):

(8)

Of course, (7) is too good to hold for an arbitrary , but suppose for a
moment that our  satises it. Then we can eliminate step by step all the
variables X1  : : :  Xn like this:
(F x) j=  !  i 8X1 : : :  Xn;1 2 P (T1 X1 ^ : : : ^ Tn;1 Xn;1 !
x 2 (X1  : : :  Xn;1  Tn))
i : : : (by the same argument)
i x 2 (T1  : : :  Tn):

24

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

And the last relation can be e ectively rewritten in the form of a rst order
formula (x) in R and = having x as its only free variable. So, nally we
shall have F j=  !  i 8x (x).
Now, to satisfy (7),  should have the property that all its operators
distribute over intersections. Clearly, ! and : are not suitable for this goal.
But all the other operators turn out to be good enough at least in descriptive
and Kripke frames. So we can take as  any positive modal formula. The
main property of a positive formula '(: : :  p : : :) is its monotonicity in every
variable p which means that, for all sets X , Y of worlds in a frame, X Y
implies '(: : :  X : : :) '(: : :  Y : : :).
To prove that all positive formulas satisfy (7) in Kripke frames and descriptive frames, recall that 2 distributes over arbitrary intersections in
any frame. As to 3, we have the following lemma in which a family X of
non-empty subsets of some space W is called downward directed if for all
X Y 2 X there is Z 2 X such that Z X \ Y .
LEMMA 1.29 (Esakia 1974) Suppose F = hW R P i is a descriptive frame.
Then for every downward directed family X P ,

3

\ X = \ 3X:

X 2X

X 2X

Using Esakia's Lemma, by induction on the construction of ' one can
prove
LEMMA 1.30 Suppose that F = hW R P i is a Kripke or descriptive frame
and '(p : : :  q : : :  r) is a positive formula. Then for every Y W and all
U : : :  V 2 P ,

\f'(U : : :  X : : :  V ) : Y

X 2 Pg =
\
'(U : : :  fX 2 P : Y

X g : : :  V ):

(9)

It follows from this lemma and considerations above that Sahlqvist's Theorem holds for formulas ' =  !  with strongly positive  and positive
. The remaining part of the proof is purely syntactic manipulations with
modal and rst order formulas.
Notice that using the monotonicity of positive formulas, equivalence (6)
can be generalized to the following one: for every F = hW R P i, every
positive i (: : :  p : : :) and every xi 2 W ,
8X 2 P (Y

_ xi 2 i(: : :  X : : :)) i
_i xni 2 \fi(: : :  X : : :) : Y

X!



in

X 2 P g:

(10)

ADVANCED MODAL LOGIC

25

Say that a modal formula  is untied if it can be constructed from negative
formulas and strongly positive ones using only ^ and 3. If (p1  : : :  pn ) is
negative then : (p1  : : :  pn ) is clearly equivalent in K to a positive formula
we denote it by (:p1  : : :  :pn ).
LEMMA 1.31 Let (p1  : : :  pn ) be an untied formula and F = hW R P i a
frame. Then for every x 2 W and all X1  : : :  Xn 2 P ,

x 2 (X1  : : :  Xn ) i 9y1  : : :  yl (# ^

^ Ti Xi ^ ^ zj 2 j (X  : : :  Xn))

in

1

j m

where the formula in the right-hand side, eectively constructed from , has
only one free individual variable x, # is a conjunction of formulas of the form
uRv, Ti are suitable R-terms and j (p1  : : :  pn ) are negative formulas.

We are ready now to prove Sahlqvist's Theorem. To construct a rst order
equivalent for 2k ( ! ) supplied by the formulation of our theorem, we
observe rst that one can equivalently reduce  to a disjunction 1 _ : : : _ m
of untied formulas, and hence 2k ( ! ) is equivalent in K to the formula
2k (1 ! ) ^ : : : ^ 2k (m ! ). So all we need is to nd a rst order
equivalent for an arbitrary formula 2k ( ! ) with untied  and positive .
Let p1  : : : pn be all the variables in  and  and F = hW R P i a descriptive
or Kripke frame. Then, for any x 2 W , we have:
(F x) j= 2k ( ! ) i 8X1  : : :  Xn 2 P x 2 2k ( ! )(X1  : : :  Xn )
(by Lemma 1.31) i 8X1  : : :  Xn 2 P 8y (xRk y ! (9y1  : : :  yl (# ^
Ti Xi ^ zj 2 j (X1  : : :  Xn )) !

^

^

in

j m

y 2 (X1  : : :  Xn )))
^
i 8X1  : : :  Xn 2 P 8y y1 : : :  yl (#0 ^ Ti Xi ^

^ zj 2 j (X  : : :  Xn) ! y 2 (X i :n: :  Xn))


j m

1

1

where #0 = xRk y ^ #. Let j (p1  : : :  pn) = j (:p1  : : :  :pn ). We continue
this chain of equivalences as follows:
i

8y y1 : : :  yl (#0 ! 8X1 : : :  Xn 2 P (

_ zj 2 j (X  : : :  Xn)))

j m+1

1

^ Ti Xi !

in

26

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

(where m+1 (p1  : : :  pn ) = (p1  : : :  pn ) and zm+1 = y)
i

8y y1 : : :  yl (#0 !

_ zj 2 j (T  : : :  Tn))

j m+1

1

as follows from (10), Lemma 1.30 and equality (5). It remains to use
Lemma 1.27.
2
The formulas ' dened in the formulation of Theorem 1.25 are called
Sahlqvist formulas. It follows from this theorem that if L is a D{persistent
logic and ; a set of Sahlqvist formulas then L  ; is also D{persistent.
Moreover, L  ; is elementary (in the sense that the class of Kripke frames
for it coincides with the class of all models for some set of rst order formulas
in R and =) whenever L is so.
Other proofs of Sahlqvist's Theorem were found by Kracht 1993] and
Jonsson 1994] (the latter is based upon the algebraic technique developed in
Jonsson and Tarski 1951]). Venema 1991] extended Sahlqvist's Theorem to
logics with non-standard inference rules, like Gabbay's 1981a] irreexivity
rule. In Chagrov and Zakharyaschev 1995b] it is shown that there is a
continuum of Sahlqvist logics above S4 and that not all of them have the
nite model property (above T such a logic was constructed by Hughes
and Cresswell 1984]). As we shall see later in this chapter, there are even
undecidable nitely axiomatizable Sahlqvist logics in NExtK. It would be
of interest to nd out whether such logics exist above K4 or S4.
Kracht 1993] described syntactically the set of rst order equivalents of
Sahlqvist formulas. To formulate his criterion we require the fragment S of
rst order logic dened inductively as follows. Formulas of the form xRm y
are in S for all variables x y and every m < ! besides, if  0 are in S then
the formulas
8x 2 y"m  9x 2 y"m  ^ 0  and _ 0

are also in S . For simplicity we assume that all occurrences of quantiers
in a formula bind pairwise distinct variables. Call a variable y in a formula
2 S inherently universal if either all occurences of y are free in or
contains a subformula 8y 2 x"m 0 which is not in the scope of 9.
THEOREM 1.32 (Kracht 1993) For every rst order formula (x) (in R
and =) of one free variable x, the following conditions are equivalent:
(i) (x) is classically equivalent to a formula 0 (x) 2 S such that any subformula of the form yRm z of 0 (x) contains at least one inherently universal
variable
(ii) (x) corresponds to a Sahlqvist formula in the sense of Theorem 1.25.

ADVANCED MODAL LOGIC

27

Condition (i) is satised, for example, by the formula
8u 2 x" 8v 2 x" 9z 2 u" vRz
which corresponds to 32p ! 23p. On the other hand,
(x) = 9y 2 x" 8z 2 y" zR0y
does not satisfy (i). In fact, even relative to S4 the condition expressed by
(x) does not correspond to any Sahlqvist formula. Notice, however, that
S4  23p ! 32p is a D-persistent logic whose frames are precisely the
transitive and reexive frames validating 8x (x).
We conclude this section by mentioning two more important results connecting persistence and elementarity (the idea of the proof was discussed in
Section 22 of Basic Modal Logic.)
THEOREM 1.33 (i) (Fine 1975b, van Benthem 1980) If a logic L is characterized by a rst order denable class of Kripke frames then L is D{
persistent.
(ii) (Fine 1975b) If L is R-persistent then the class of Kripke frames for
L is rst order denable.
It is an open problem whether every D{persistent logic is determined by
a rst order denable class of Kripke frames for more information about
this and related problems consult Goldblatt 1995].

1.4 The degree of Kripke incompleteness
All known logics in NExtK of \natural origin" are complete with respect

to Kripke semantics. On the other hand, there are many examples of \articial" logics that cannot be characterized by any class of Kripke frames
(see Sections 19, 20 of Basic Modal Logic or the examples below). To understand the phenomenon of Kripke incompleteness Fine 1974b] proposed
to investigate how many logics may share the same Kripke frames with a
given logic L. The number of them is called the degree of Kripke incompleteness of L. Of course, this number depends on the lattice of logics under
consideration. The degree of Kripke incompleteness of logics in NExtK was
comprehensively studied by Blok 1978]. In this section we present the main
results of that paper following Chagrov and Zakharyaschev 1997].
By Theorem 1.12, all Kripke complete union-splittings of NExtK have
degree of incompleteness 1. And it turns out that no other union-splitting
exists.
THEOREM 1.34 (Blok 1978) Every union-splitting of NExtK has the nite
model property.

28

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

nontransitive

x1 -x11


6

xk;1 xk

     1 - 1

x1 -x2


6

x

x1

x1

x1

xk

xk

xk

     n - 1 - 2    n    1 - 2    n

(a)

(b)
Figure 3.

Proof Let F be a class of nite rooted cycle free frames. We prove that
L = K=F has the nite model property using a variant of ltration, which

is applied to an n-generated rened frame F = hW R P i for L refuting a
formula '(p1  : : :  pn ) under a valuation V.
Since F is di erentiated, for every m 1 there are only nitely many
points x in F such that x j= 2m ? ^ :2m;1 ? we shall call them points of
type m. Given
Sub', Sub' the set of all subformulas in ', we put
m = m if m is the minimal number such that a point in F is of type  m
whenever x j= and the formulas in Sub' ; are false at x (under V) if
no such m exists, we put m = 0. Let
k = maxfm :
Sub'g ; = Sub(' ^ 2k ?):
Now we divide F into two parts: W1 consisting of points of type  k and
W2 = W ; W1 . For x y 2 W , put x  y if either x y 2 W1 and x = y
or x y 2 W2 and exactly the same formulas in ; are true at x and y. Let
N = hG Ui be the smallest ltration (see Section 12 of Basic Modal Logic)
of M = hF Vi through ; with respect to . Since W1 is nite, G is also
nite and, by the Filtration Theorem, (M x) j=  i (N x]) j= , for every
 2 ;. So it remains to show that G j= L. Notice that x] in G is of type
m  k i x has type m in F. Moreover, there is no x] of type l > k. For
otherwise x 6j= 2k ? and m = 0 for = f 2 Sub' : x j= g, which
means that arbitrary long chains (of not necessarily distinct points) start
from x], contrary to x] being of type l. Thus G consists of two parts:
points of type  k, which form the generated subframe hW1  R W1 i of F,
and points involved in cycles. Since F j= L and frames in F are cycle free,
it follows from Lemma 1.13 and Theorem 1.17 that G j= L.
2
THEOREM 1.35 (Blok 1978) If a logic L is inconsistent or a union-splitting
of NExtK, then L is strictly Kripke complete. Otherwise L has degree of
Kripke incompleteness 2@0 in NExtK.

Proof That For is strictly complete follows from Example 1.10 and Theorem 1.12. Suppose now that a consistent L is not a union-splitting and L0

ADVANCED MODAL LOGIC

29

is the greatest union-splitting contained in L. Since L0 has the nite model
property, there is a nite rooted frame F = hW Ri for L0 refuting some
' 2 L and such that every proper generated subframe of F validates L.
Clearly, F is not cycle free. Let x1 Rx2 R : : : Rxn Rx1 be the shortest cycle
in F and k = md(') + 1. We construct a new frame F0 by extending the
cycle x1  : : :  xn  x1 as is shown in Fig. 3 ((a) for n = 1 and (b) for n > 1).
More precisely, we add to F copies x1i  : : :  xki of xi for each i 2 f1 : : : ng,
organize them into the nontransitive cycle shown in Fig. 3 and draw an
arrow from xji to y 2 W ;fx1  : : :  xn g i xi Ry. Denote the resulting frame
by F0 = hW 0  R0 i and let x0 = xkn . By the construction, F is a reduct of F0 .
Therefore, for every models M = hF Vi and M0 = hF0  V0 i such that

V0 (p) = V(p)  fxji : xi 2 V(p) j < kg

and for every x 2 W ,  2 Sub', we have (M x) j=  i (M0  x) j= . So we
can hook some other model on x0 , and points in W will not feel its presence
by means of ''s subformulas. The frame to be hooked on x0 depends on
whether  j= L or  j= L. We consider only the former alternative.
Fix some m > jW 0 j. For each I ! ; f0g, let FI = hWI  RI  PI i be the
frame whose diagram is shown in Fig. 4 (d0 sees the root of F0 , all points
ei and e0j and is seen from x0  the subframes in dashed boxes are transitive,
e0i 2 WI i i 2 I , and PI consists of sets of the form X  Y such that X
is a nite or conite subset of WI ; fb ai : i < !g and Y is either a nite
subset of fai : i < !g or is of the form fbg Y 0 , where Y 0 is a conite subset
of fai : i < !g. It is not hard to see that the points ai , c, ei and e0i are
characterized by the variable free formulas

0 = 3( m ^ 3( m;1 ^ : : : ^ 3 0) : : :) ^ :32( m ^ 3( m;1 ^ : : : ^ 3 0) : : :)
i+1 = 3i ^ :32 i   = 320 ^ :30
0 = 3 i+1 = 3i ^ :32i  0i+1 = 3i ^ :3+i+1 
(in the sense that x j= i i x = ai , etc.), where
0

= 32? 1 = 3 0 ^ : 0  2 = 3 1 ^ : 1 ^ :3+ 0 
k+1 = 3 k ^ : k ^ :3+ k;1 ^ : : : ^ :3+ 0 :

Dene LI to be the logic determined by the class of frames for L and FI ,
i.e., LI = L \ LogFI . Since :(0i ^ 3m+6:') 2 LJ ; LI for i 2 I ; J (' is
refuted at the root of F0 ), jfLI : I ! ; f0ggj = 2@0 .
Let us show now that LI has the same Kripke frames as L. Since LI L,
we must prove that every Kripke frame for LI validates L. Suppose there
is a rooted Kripke frame G such that G j= LI but G 6j= , for some  2 L.

30

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

nontransitive

F0

x
H
transitive
6H
H
c -b
a
a a d d d  d

     -i -    1 -0 -m   1 -0  -;1
6

e

0

e    
1

I
@
@

transitive

e

j ;

0

  9



@;0

ej

Figure 4.
Since  is in L, it is valid in all frames for L, in particular,  j= . And
since  62 LI ,  is refuted in FI . Moreover, by the construction of FI , it
is refuted at a point from which the root of F0 can be reached by a nite
number of steps. Therefore, the following formulas are valid in FI and so
belong to LI and are valid in G:

_l 3i

(11)

^l 2i( ! 2(2 (2 p ! p) ! p))

(12)

: !
: !

i=0

i=0

0

0

where p does not occur in  and l is a suciently big number so that
any point in FI is accessible by  l steps from every point in the selected
cycle and every point at which  may be false, and 20  = 2(30 ! ).
According to (11), G contains a point at which  is true. By the construction
of  , this point has a successor y at which, by (12), 20 (20 p ! p) ! p is
true under any valuation in G and y j= 30. Dene a valuation U in G
by taking U(p) = y ". Then y j= 20 (20 p ! p), from which y j= p and so
y 2 y ". Now dene another valuation U0 so that U0(p) = y " ;fyg. Since
y is reexive, we again have y j= 20 (20 p ! p), whence y j= p, which is a
contradiction.
2
This construction can be used to obtain one more important result.
THEOREM 1.36 (Blok 1978) Every union-splitting K=F has {  @0 immediate predecessors in NExtK, where { is the number of frames in F which
are not reducts of generated subframes of other frames in F . Every consistent logic dierent from union-splittings has 2@0 immediate predecessors in
NExtK. (For has 2 immediate predecessors in NExtK.)

ADVANCED MODAL LOGIC

31

Proof The former claim follows from Theorem 1.12. To establish the

latter, we continue the proof of Theorem 1.35. One can show that L is
nitely axiomatizable over LI (the proof is rather technical, and we omit it
here). Then, by Zorn's Lemma, NExtLI contains an immediate predecessor
L0I of L. Besides, LI  LJ = L whenever I 6= J . Indeed,

LI  LJ = (L \ LogFI )  (L \ LogFJ ) = L \ (LogFI  LogFJ )
and if i 2 I ; J then, for every  2 L and a suciently big l,
:

_l 3k !  2 LogFI  : 2 LogFJ 
0

k=0

i

0

i

from which  2 LogFI  LogFJ and so L LogFI  LogFJ . It follows that
L0I 6= L0J whenever I 6= J .
2

It is worth noting that tabular logics, proper extensions of D and extensions of K4 are not union-splittings in NExtK. Similar results hold for
the lattices NExtD and NExtT, where every consistent logic has degree of
incompleteness 2@0 (see Blok 1978, 1980b]). It would be of interest to describe the behavior of this function in NExtK4, NExtS4, NExtGrz (where
Theorem 1.34 does not hold and where every tabular logic has nitely many
immediate predecessors) and other lattices of logics to be considered later
in this chapter.

1.5 Stronger forms of Kripke completeness

In the two preceding sections we were considering the problem of characterizing logics L 2 NExtK by classes of Kripke frames. The same problem
arises in connection with the two consequence relations `L and `L as well.
Theorem 1.19 shows the way of introducing the corresponding concepts of
completeness.
With each Kripke frame F let us associate a consequence relation j=F by
putting, for any formula ' and any set ; of formulas, ; j=F ' i (M x) j= ;
implies (M x) j= ' for every model M based on F and every point x in F.
Clearly, a modal logic L is Kripke complete i , for any nite set of formulas
; and any formula ', ; 6`L ' only if there is a Kripke frame F for L such
that ; 6j=F '. Now, let us call L strongly Kripke complete7 if this implication
holds for arbitrary sets ;. In other words, L is strongly complete if every Lconsistent set of formulas holds at some point in a model based on a Kripke
frame for L. Another reformulation: L is strongly complete i L is Kripke
7 Fine 1974c] calls such logics compact, which does not agree with the use of this term
by Thomason 1972].

32

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

T

complete and the relation fj=F: F is a Kripke frame for Lg is nitary. It
follows from the construction of the canonical models that every canonical
(in particular, D{persistent) logic is strongly complete, which provides us
with many examples of such logics in NExtK.
By Theorem 1.33, all logics characterized by rst order denable classes
of Kripke frames are strongly complete. The converse does not hold: there
exist strongly complete logics which are not canonical. The simplest is the
bimodal logic of the frame hR < >i  see Example 2.39 below. By applying
the Thomason simulation (to be introduced in Section 2.3) to this logic
we obtain a logic in NExtK with the same properties see Theorem 2.18.
Moreover, in contrast to D{persistence, strong Kripke completeness is not
preserved under nite sums of logics (see Wolter 1996c]). It is an open
problem, however, whether such logics exist in NExtK4.
Perhaps the simplest examples of Kripke complete logics which are not
strongly complete are GL and Grz (use Theorem 1.58 and the fact that
these logics are not elementary see Correspondence Theory). It is much
more dicult to prove that the McKinsey logic K  23p ! 32p is not
strongly complete the proof can be found in Wang 1992]. For other examples of modal logics that are not strongly complete see Section 3.4. It
is worth noting also that, as was shown in Fine 1974c], every nite width
logic in a nite language turns out to be strongly Kripke complete, though
this is not the case for logics in an innite language, witness
GL:3 = GL  2(2+p ! q) _ 2(2+q ! p):
For the consequence relation `L, we should take the \global" version j=F
of j=F . Namely, we put ; j=F ' if M j= ; implies M j= ' for any model M
based on F. A modal logic L is called globally Kripke complete if for any
nite set of formulas ; and any formula ', ; 6`L ' only if there is a frame
F for L such that ; 6j=F '. L is strongly globally complete if this holds for
arbitrary (not only nite) ;. We also say that L has the global nite model
property if for every nite ; and every ', ; 6`L ' only if there is a nite
frame F for L such that ; 6j=F '.
The global nite model property (FMP, for short) of many standard logics
can be proved by ltration. Say that a logic L strongly admits ltration if for
every generated submodel M of the canonical model ML and every nite set
of formulas # closed under subformulas, there is a ltration of M through
# based on a frame for L.
PROPOSITION 1.37 (Goranko and Passy 1992) If L strongly admits ltration then L has global FMP.
Proof Suppose that ; 6`L ', ; nite. Then 2<! ; 6`L ' and so the
set = 2<! ;  f:'g is L-consistent. It remains to ltrate through

V

V

ADVANCED MODAL LOGIC

33

Sub;  Sub' the submodel of ML generated by a maximal L-consistent
2

set containing .

It follows in particular that K, T, D, KB have global FMP.
PROPOSITION 1.38 Suppose L is globally complete (has global FMP) and
; is a nite set of variable free formulas. Then L  ; is globally complete
(has global FMP) as well.

Proof Let L0 = L  ; and 6`L ', nite. Then ;  6`L ' and so
0

there exists a (nite) Kripke frame F for L such that ;  6j=G '. Since ;
contains no variables, F j= L0 .
2

For n-transitive logics L the global consequence relation `L is reducible to
the \local" `L and so L is Kripke complete (has FMP, is strongly complete)
i L is globally complete (has global FMP, is strongly globally complete). In
general the global properties are stronger than the \local" ones. Although
L is globally complete (has global FMP) only if L is complete (has FMP),
the converse does not hold (see Wolter 1994a] and Kracht 1996]).
EXAMPLE 1.39 Let L = Alt3  p ! 23p  (2p ^ :p) ! :(3q ^ 3:q). A
Kripke frame F validates L i no point in F has more than three successors,
F is symmetric, and irreexive points in it have at most one successor. By
Proposition 1.22, L is Kripke complete. The class of Kripke frames for L is
closed under (not necessarily generated) subframes. So, by Proposition 1.59
to be proved below, L has FMP. We show now that it does not have global
FMP. To this end we require the formulas:

1 = q1 ^ :q2 ^ :q3  2 = :q1 ^ q2 ^ :q3  3 = :q1 ^ :q2 ^ q3 

^

' = 2p ^ :p ^ 1   = fi ! 3i+1 : i = 1 2g ^ 3 ! 31:
Let F = hW Ri, where W = ! and
R = fhm mi : m > 0g  fhm m + 1i : m < !g  fhm m ; 1i : m > 0g:
We then have  6j=F :'. In fact, ' is true at 0 and  is true everywhere
under the valuation V dened by V(p) = W ; f0g and V(qi ) = f3n + i :
n < !g. Clearly, F j= L and so  6`L :'. Suppose now that (N x0 ) j= '
and N j= , for a model N based on a Kripke frame G = hV S i for L. Then
we can nd a sequence xj , j < !, such that xj Sxj+1 and x3j+i j= i+1 , for
j < ! and i = 1 2 3. The reader can verify that all points xj are distinct.
Let us consider now the algebraic meaning of the notions introduced
above. A logic L is Kripke complete i the variety AlgL of modal algebras

34

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

for L is generated by the class KrL = fF+ : F is a Kripke frame for Lg. By
Birkho 's Theorem (see e.g. Mal'cev 1973]), this means that
AlgL = HSPKrL
(i.e., AlgL is obtained by taking the closure of KrL under direct products, then the closure of the result under (isomorphic copies of) subalgebras
and nally under homomorphic images). Clearly, L is globally complete i
precisely the same quasi-identities hold in KrL and AlgL. And since the
quasi-variety generated by a class of algebras C is SPPU C (where PU denotes
the closure under ultraproducts see Mal'cev 1973]), L is globally complete
i
AlgL = SPPU KrL:
Goldblatt 1989] calls the variety AlgL complexif AlgL = SKrL, or, equivalently, if AlgL = SPKrL (this follows from the fact that the dual of the
disjoint union of a family of Kripke frames fFi : i 2 I g is isomorphic to the
product i2I F+i ). We say a logic L is {-complex, { a cardinal, if every
modal algebra for L with  { generators is a subalgebra of F+ for some
Kripke frame F j= L. As was shown in Wolter 1993], this notion turns
out to be the algebraic counterpart of both strong completeness and strong
global completeness of logics in innite languages with { variables.

Q

THEOREM 1.40 For every normal modal logic L in an innite language
with { variables the following conditions are equivalent:
(i) L is strongly Kripke complete
(ii) L is globally strongly complete
(iii) L is {-complex.
Proof (i) ) (iii) Suppose the cardinality of A 2 AlgL does not exceed {.
Denote by L the algebra of modal formulas over { propositional variables
and take some homomorphism h from L onto A. For each ultralter r in
A, the set h;1 (r) is maximal L-consistent. Since L is strongly complete,
there is a model Mr = hFr  Vr i with root xr based on a Kripke frame
Fr for L and such that (Mr  xr ) j= h;1 (r). Without loss of generality we
may assume that the frames Fr for distinct r are disjoint. Let F be the
disjoint union of all of them. Dene a homomorphism V from L into F+ by
taking
V(p) = fVr (p) : r is an ultralter in Ag:
Then V(L) is a subalgebra of F+ 2 AlgL isomorphic to A.
The implication (iii) ) (ii) is trivial. To prove (ii) ) (i), consider an
L-consistent set of formulas ; of cardinality  { and put
= fpg  f2n(p ! ') : n < ! ' 2 ;g



ADVANCED MODAL LOGIC

35

where the variable p does not occur in formulas from ;. It is easily checked
that all nite subsets of are L-consistent, so is L-consistent too. It
follows that fp ! ' : ' 2 ;g 6`L :p. And since L is globally strongly
complete, there exists a model M based on a Kripke frame for L such that
M j= fp ! ' : ' 2 ;g and (M x) j= p, for some x. But then (M x) j= ;.

2

1.6 Canonical formulas
The main problem of completeness theory in modal logic is not only to nd
a suciently simple class of frames with respect to which a given logic L is
complete but also to characterize the constitution of frames for L (in this
class). The rst order approach to the characterization problem, discussed
in Section 1.3 in connection with Sahlqvist's Theorem, comes across two
obstacles. First, there are formulas whose Kripke frames cannot be described in the rst order language with R and =. The best known example
is probably the Lob axiom

la = 2(2p ! p) ! 2p:
F j= la i F is transitive, irreexive (i.e., a strict partial order) and Noetherian in the sense that it contains no innite ascending chain of distinct
points. And as is well known, the condition of Noetherianness is not a rst
order one. The second obstacle is that this approach deals only with logics that are Kripke complete it does not take into account sets of possible
values.
There is another, purely frame-theoretic method of characterizing the
structure of frames. For instance, a frame G validates K=F i G does
not contain a generated subframe reducible to F. It was shown in Zakharyaschev 1984, 1988, 1992] that in a similar manner one can describe
transitive frames validating an arbitrary modal formula. It is not clear
whether characterizations of this sort can be extended to the class of all
frames (an important step in this direction would be a generalization to
n-transitive frames). That is why all frames in this section are assumed to
be transitive. First we illustrate this method by a simple example.
EXAMPLE 1.41 Suppose a frame F = hW R P i refutes la under some
valuation. Then the set V = fx 2 W : x 6j= lag is in P and V V #. It
follows from the former that G = hV R V fX \ V : X 2 P gi is a frame|
we call it the subframe of F induced by V . And the latter condition means
that G is reducible to the single reexive point  which is the simplest
refutation frame for la. Moreover, one can readily check that the converse
also holds: if there is a subframe G of F reducible to  then F 6j= la.

36

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

This example motivates the following denitions. Given frames F =
hW R P i and G = hV S Qi, a partial (i.e., not completely dened, in
general) map f from W onto V is called a subreduction of F to G if it
satises the reduction conditions (R1){(R3) for all x and y in the domain
of f and all X 2 Q. The domain of f will be denoted by domf . In other
words, an f -subreduct of F is a reduct of the subframe of F induced by
domf . A frame G = hV S Qi is a subframe of F = hW R P i if V W and
the identity map on V is a subreduction of F to G, i.e., if S = R V and
Q P . Note that a generated subframe G of F is not in general a subframe
of F, since V may be not in P .
Thus, the result of Example 1.41 can be reformulated like this: F 6j= la
i F is subreducible to .
A subreduction f of F to G is called conal if
domf " domf #:
This important notion can be motivated by the following observation: F
refutes 3> i F is conally subreducible to  (a plain subreduction is not
enough).
THEOREM 1.42 Every refutation frame F = hW R P i for '(p1  : : :  pn ) is
conally subreducible to a nite rooted refutation frame for ' containing at
most c' = 2n  (cn (1) + : : : + cn (2jSub'j)) points.8

Proof Suppose ' is refuted in F under a valuation V. Without loss

of generality we can assume F to be generated by V(p1 ) : : :  V(pn ). Let
X1  : : :  Xm be all distinct maximal 0-cyclic sets in F. Clearly, m  cn (1)
but unlike Theorem 1.8, F is not in general rened and so these sets are
not necessarily clusters of depth 1. However, they can be easily reduced
to such clusters. Dene an equivalence relation  on W by putting x  y
i x = y or x y 2 Xi , for some i 2 f1 : : : mg, and x  y (as before
# = fp1  : : :  pn g). Let x] be the equivalence class under  generated by
x and X ] = fx] : x 2 X g, for X 2 P . By the denition of cyclic sets,
xRy i x] y] #. So the map x 7! x] is a reduction of F to the frame
F01 = hW10  R10  P10 i which results from F by \folding up" the 0-cyclic sets Xi
into clusters of depth 1 and leaving the other points untouched: W10 = W ],
x]R10 y] i x] y] # and P10 = fX ] : X 2 P g. (Roughly, we rene that
part of F which gives points of depth 1.) Put V01 (pi ) = V(pi )]. Then by
the Reduction (or P-morphism) Theorem, we have x j=  i x] j= , for
every  2 Sub'.
Let X be the set of all points in F01 of depth > 1 having Sub'-equivalent
successors of depth 1. It is not hard to see that X 2 P10 . Denote by
8

The function cn (m) was dened in Section 1.2.

ADVANCED MODAL LOGIC

37

F1 = hW1  R1  P1 i the subframe of F01 induced by W10 ; X and let V1 be the
restriction of V01 to F1 . By induction on the construction of  2 Sub' one
can readily show that  has the same truth-values at common points in F01
and F1 (under V01 and V1 , respectively) and so F1 6j= '. The partial map
x 7! x], for x] 2 W1 , is a conal subreduction of F to F1 .
Then we take the maximal 1-cyclic sets in F1 , \fold" them up into clusters
of depth 2 and remove those points of depth > 2 that have Sub'-equivalent
successors of depth 2. The resulting frame F2 will be a conal subreduct of
F1 and so of F as well. After that we form clusters of depth 3, and so forth.
In at most 2jSub'j steps of that sort we shall construct a conal subreduct
of F refuting ' and containing  c' points. It remains to select in it a
suitable rooted generated subframe.
2
For the majority of standard modal axioms the converse also holds.
However, not for all. The simplest counterexample is the density axiom
den = 22p ! 2p. It is refuted by the chain H of two irreexive points but
becomes valid if we insert between them a reexive one. In fact, F 6j= den
i there is a subreduction f of F to H such that f (x") = fag, for no point
x in domf ";domf , where a is the nal point in H.
Loosely, every refutation frame for formulas like la can be constructed by
adding new points to a frame G that is reducible to some nite refutation
frame of xed size. For formulas like 3> we have to take into account the
conality condition and do not put new points \above" G. And formulas
like den impose another restriction: some places inside G may be \closed"
for inserting new points. These \closed domains" can be singled out in the
following way.
Suppose N = hH Ui is a model and a an antichain in H. Say that a is
an open domain in N relativeVto a formula
if there is a pair ta = (;a  a )
W a 62' K4
such that ;a  a = Sub', ;a !
and
 2 2 ;a implies  2 ;a ,
 2 2 ;a i a j= 2+  for all a 2 a.
Otherwise a is called a closed domain in N relative to '. A reexive singleton
a = fag is always open: just take ta = (f 2 Sub' : a j= g f 2 Sub' :
a 6j= g). It is easy to see also that antichains consisting of points from the
same clusters are open or closed simultaneously we shall not distinguish
between such antichains.
For a frame H and a (possibly empty) set D of antichains in H, we say a
subreduction f of F to H satises the closed domain condition for D if
(CDC) :9x 2 domf "; domf 9d 2 D f (x") = d".
Notice that the conal subreduction f of F to the resulting nite rooted
frame H in the proof of Theorem 1.42 satises (CDC) for the set D of

38

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

closed domains in the corresponding model N on H refuting '. Indeed,
every x 2 domf " ; domf has a Sub'-equivalent successor y 2 domf ,
and so an antichain d such that f (x ") = d" is open, since we can take
td = (f 2 Sub' : y j= g f 2 Sub' : y 6j= g). On the other hand, we
have
PROPOSITION 1.43 Suppose N = hH Ui is a nite countermodel for '
and D the set of all closed domains in N relative to '. Then F 6j= '
whenever there is a conal subreduction f of F to H satisfying (CDC) for
D. Moreover, if ' is negation free (i.e., contains no ?, :, 3) then a plain
subreduction satisfying (CDC) for D is enough.
Proof If f is conal and F = hW R P i then we can assume domf " = W .
Dene a valuation V in F as follows. If x 2 domf then we take x j= p i
f (x) j= p, for every variable p in '. If x 62 domf then f (x") 6= , since f is
conal. Let a be an antichain in H such that a" = f (x"). By (CDC), a is
an open domain in N, and we put y j= p i p 2 ;a, for every y 62 domf such
that f (y ") = f (x"). One can show that V is really a valuation in F and,
for every  2 Sub', x j=  i f (x) j=  in the case x 2 domf , and x j= 
i  2 ;a , where a is the open domain in N associated with x, in the case
x 62 domf .
If ' is negation free and f is a plain subreduction then f (x ") may be
empty. In such a case we just put x j= p, for all variables p.
2
Now let us summarize what we have got. Given an arbitrary formula
', we can e ectively construct a nite collection of nite rooted frames
F1  : : :  Fn (underlying all possible rooted countermodels for ' with  c'
points) and select in them sets D1  : : :  Dn of antichains (open domains in
those countermodels) such that, for any frame F, F 6j= ' i there is a conal
subreduction of F to Fi , for some i, satisfying (CDC) for Di . If ' is negation
free then a plain subreduction satisfying (CDC) is enough.
This general characterization of the constitution of refutation transitive
frames can be presented in a more convenient form if with every nite rooted
frame F = hW Ri and a set D of antichains in F we associate formulas
(F D ?) and (F D) such that G 6j= (F D ?) (G 6j= (F D)) i there is
a conal (respectively, plain) subreduction of G to F satisfying (CDC) for
D. For instance, one can take

(F D ?) =

^ 'ij ^ ^n 'i ^ ^ 'd ^ ' ! p

d2D
where a0  : : :  an are all points in F and a0 is its root,
ai Raj

i=0

'ij = 2+ (2pj ! pi )

?

0

ADVANCED MODAL LOGIC

'i = 2+ ((

^ 2pk ^ ^n pj ! pi) ! pi

:ai Rak

39

j =0j 6=i

^ 2pj ^ ^n pi ! _ 2pj )
'd = 2 (
+

'?

i=0
ai 2W ;d"
n
= 2+ ( 2+ pi ! ?):
i=0

^

aj 2d

(F D) results from (F D ?) by deleting the conjunct '? . (F D ?) and
(F D) are called the canonical and negation free canonical formulas for F
and D, respectively. It is not hard to check that if (F D ?) is refuted in
G = hV S Qi under some valuation then the partial map dened by x 7! ai
if the premise of (F D ?) is true at x and pi false is a conal subreduction
of G to F satisfying (CDC) for D and conversely, if f is such a subreduction
then the valuation U dened by U(pi ) = V ; f ;1 (ai ) refutes (F D ?) at
any point in f ;1 (a0 ).
THEOREM 1.44 There is an algorithm which, given a formula ', returns
canonical formulas (F1  D1  ?) : : :  (Fn  Dn  ?) such that
K4  ' = K4  (F1 D1  ?)  : : :  (Fn  Dn ?):
So the set of canonical formulas is complete for the class NExtK4. If ' is
negation free then one can use negation free canonical formulas.

It is not hard to see that K4  ' is a splitting of NExtK4 i ' is deductively equivalent in NExtK4 to a formula of the form (F D]  ?), where D]
is the set of all antichains in F (in this case K4=F = K4  (F D]  ?)). Such
formulas are known as Jankov formulas (Jankov 1963] introduced them for
intuitionistic logic), or frame formulas (cf. Fine 1974a]), or Jankov{Fine
formulas. Since GL is not a union-splitting of NExtK4, this class of logics
has no axiomatic basis.
We conclude this section by showing in Table 2 canonical axiomatizations
of some standard modal logics in the eld of K4. For brevity we write
(F ?) instead of (F  ?) and ] (F ?) instead of (F D]  ?). Each in
the table is to be replaced by both  and .
For more information about the canonical formulas the reader is referred
to Zakharyaschev 1992, 1997b].

1.7 Decidability via the nite model property

Although, for cardinality reason, there are \much more" undecidable logics
than decidable ones, almost all \natural" propositional systems close to

40

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

D4
S4
GL
Grz
K4:1

=
=
=
=
=

Triv
Verum
S5
K4B
A
K4:2
K4:3
Dum

K4  ( ?)
K4  ()
K4  ()

K4  ()  ( ) 
K4  ( ?)  (  ?)
 
= K4  ()  ( )  ( 6)


= K4  ()  ( 6)

= S4  ( 6)

= K4  ( 6) (4 axioms)
1 2
K 
A

= GL  ( A  ff1g f1 2gg)

6

K 
A

6
= K4  (   ?)  ( 6 ?)  ( A   ?) (8 axioms)
K 
A


= K4  ( A ) (6 axioms)

 
6
= S4  ( AK )  ( )

z n}|  {
+1

I

;
@;
K4BWn = K4  ( @
) (2n + 4 axioms)

n

K4BDn
K4nm

..6
.
1
= K4  ( 60 ) (2n+1 axioms)
m
..6
.
1
= K4  ( 60  D] )

Table 2. Canonical axioms of standard modal logics

ADVANCED MODAL LOGIC

41

those we deal with in this chapter turn out to be decidable. Relevant and
linear logics are probably the best known among very few exceptions (see
Urquhart 1984], Lincoln et al. 1992]).
The majority of decidability results in modal logic was obtained by means
of establishing the nite model property. FMP by itself does not ensure yet
decidability (there is a continuum of logics with FMP) some additional conditions are required to be satised. For instance, to prove the decidability
of S4 McKinsey 1941] used two such conditions: that the logic under consideration is characterized by an e ective class of nite frames (or algebras,
matrices, models, etc.) and that there is an e ective (exponential in the case
of S4) upper bound for the size of minimal refutation frames. Under these
conditions, a formula belongs to the logic i it is validated by (nite) frames
in a nite family which can be e ectively constructed. Another sucient
condition of decidability is provided by the following well known
THEOREM 1.45 (Harrop 1958) Every nitely axiomatizable logic with FMP
is decidable.
Here we need not to know a priori anything about the structure of frames
for a given logic. This information is replaced by checking the validity of its
axioms in nite frames, and the restriction of the size of refutation frames
is replaced by constructing all possible derivations: in a nite number of
steps we either separate a tested formula from the logic or derive it. Note
that unlike the previous case now we cannot estimate the time required to
complete this algorithm.
The condition of nite axiomatizability in Harrop's Theorem cannot be
weakened to that of recursive axiomatizability. For there is a logic of depth
3 in NExtK4 (i.e., a logic in NExtK4BD3 ) with an innite set of independent axioms so the logic of depth 3 axiomatizable by some recursively
enumerable but not recursive sequence of formulas in this set is undecidable and has FMP. On the other hand there are examples of undecidable
logics characterized by decidable classes of nite frames (see e.g. Chagrov
and Zakharyaschev 1997]). Yet one can generalize Harrop's Theorem in
the following way. A logic is decidable i it is recursively enumerable and
characterized by a recursive class of recursive algebras. However, this criterion is absolutely useless in its generality. In this connection we note two
open problems posed by Kuznetsov 1979]. Is every nitely axiomatizable
logic characterized by recursive algebras? Is every nitely axiomatizable
logic, characterized by recursive algebras, decidable? (That nite axiomatizability is essential here is explained by the following fact: if a lattice
of logics contains a logic with a continuum of immediate predecessors then
there is no countable sequence of algebras such that every logic in the lattice
is characterized by one of its subsequences. For details see Chagrov and
Zakharyaschev 1997].)

42

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

FMP of almost all standard systems was proved using various forms of
ltration (consult Section 12 Basic Modal Logic and Gabbay 1976]). However, the method of ltration is rather capricious one needs a special craft
to apply it in each particular case (for instance, to nd a suitable \lter").
In this and two subsequent sections we discuss other methods of proving
FMP which are applicable to families of logics and provide in fact sucient
conditions of FMP. (It is to be noted that the families of Kripke complete
logics considered in Section 1.3 contain logics without FMP.) A pair of such
conditions was already presented in Basic Modal Logic:
THEOREM 1.46 (Segerberg 1971) Each logic in NExtK4 characterized by
a frame of nite depth (or, which is equivalent, containing K4BDn , for
some n < !) has FMP.
THEOREM 1.47 (Bull 1966b, Fine 1971) Each logic in NExtS4:3 has FMP
and is nitely axiomatizable (and so decidable).
The former result, covering a continuum of logics, follows immediately
from the description of nitely generated rened frames for K4 in Section 1.2
and the latter is a consequence of Theorem 1.52 and Example 1.54 below.
It is worth noting also that since FL(n) is nite for every logic L 2 NExtK4
of nite depth and every n < !, there are only nitely many pairwise nonequivalent in L formulas of n variables. Logics with this property are called
locally tabular (or locally nite). Moreover, as was observed by Maksimova
1975a], the converse is also true: if L 2 NExtK4 has frames of any depth
< ! then the formulas in the sequence '1 = p, 'n+1 = p _ 2(p ! 2'n )
are not equivalent in L. Thus, a logic in NExtK4 is locally tabular i it
is of nite depth. For L 2 NExtS4 this criterion can be reformulated in
the following way: L is not locally tabular i L Grz:3, where Grz:3 =
S4:3  Grz. Likewise, L 2 NExtGL is not locally tabular i L GL:3.
Nagle and Thomason 1985] showed that all normal extensions of K5 are
locally tabular.

Uniform logics Fine 1975a] used a modal analog of the full disjunctive
normal form for constructing nite models and proving FMP of a family
of logics in NExtD (containing in particular the McKinsey system K 
23p ! 32p which had resisted all attempts to prove its completeness by

the method of canonical models and ltration). Let us notice rst that every
formula '(p1  : : :  pm) is equivalent in K either to ? or to a disjunction
of normal forms (in the variables p1  : : :  pm) of degree md('), which are
dened inductively in the following way. NF0 , the set of normal forms of
degree 0, contains all formulas of the form :1 p1 ^ : : : ^ :m pm , where each

ADVANCED MODAL LOGIC

43

:i is either blank or :. NFn+1 , the set of normal forms of degree n + 1,
consists of formulas of the form

 ^ :1 31 ^ : : : ^ :k 3k 
where S2 NF0 and 1  : : :  k are all distinct
normal forms in NFn . Put
NF = n<! NFn . Using the fact that Wf3 :  2 NFng 2 D it is not
hard to see also that in D every formula ' with md(')  n is equivalent
either to ? or to a disjunction of normal forms of degree n such that at
least one of :1  : : :  :k in the inductive step of the denition above is blank.
Such normal forms are called D-suitable.
It should be clear that, for any distinct 0  00 2 NFn , :(0 ^ 00 ) 2 K.
Consequently, for every  2 NFn and every '(p1  : : :  pm ) with md(')  n,
we have either  ! ' 2 K or  ! :' 2 K.
With each D-suitable normal form  we associate a model M = hF  V i
on a frame F = hW  R i by taking

W = f>g  f0 2 NF : 0 <n  for some n 0g
0 < 00 i 30 is a conjunct of 00 
0 R 00 i either 0 > 00 or md(0 ) = 0 and 00 = >
V (p) = f0 2 W : p is a conjunct of 0 g:
According to the denition, > is the reexive last point in F and so F is
serial. By a straightforward induction on the degree of 0 2 W one can
readily show that (M  0 ) j= 0 . It follows immediately that D has FMP.
Indeed, given ' 62 D, we reduce :' to a disjunction of D-suitable normal
forms with at least one disjunct , and then (M  ) j= .

It turns out that in the same way we can prove FMP of all logics in
NExtD axiomatizable by uniform formulas, which are dened as follows.
Every ' without modal operators is a uniform formula of degree 0 and if
' = (#1 1  : : :  #m m ), where #i 2 f2 3g, md((p1  : : :  pm)) = 0 and
1  : : :  m are uniform formulas of degree n, then ' is a uniform formula
of degree n + 1. A remarkable property of uniform formulas is the following
PROPOSITION 1.48 Suppose ' is a uniform formula of degree n and M,
N are models based upon the same frame and such that, for some point x,
(M y) j= p i (N y) j= p for every y 2 x"n and every variable p in '. Then
(M x) j= ' i (N x) j= '.
Given a logic L, we call a normal form  L-suitable if F j= L.
THEOREM 1.49 (Fine 1975a) Every logic L 2 NExtD axiomatizable by
uniform formulas has FMP.

44

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Proof It suces to prove that each formula ' with md(')  n is equivalent in L either to ? or to a disjunction of L-suitable normal forms of degree
n. And this fact will be established if we show that every D-suitable normal
form  such that  ! ? 62 L is L-suitable. Suppose otherwise. Let  be an
L-consistent and D-suitable normal form of the least possible degree under

which it is not L-suitable. Then there are a uniform formula  2 L of some
degree m and a model M = hF  Vi such that (M ) 6j= .
For every variable p in , let ;p = f0 2  "m: (M 0 ) j= pg and let
p = ;p (if ;p =  then p = ?). Observe that for every 0 2 "m we have
(M  0 ) j= p i 0 2 ;p i (M 0 ) j= p. Therefore, by Proposition 1.48,
the formula 0 which results from  by replacing each p with p is false
at  in M . Now, if md(0 ) > n then m > n and so p = ? for every p
in , i.e., 0 is variable free. But then 0 is equivalent in D to > or ?,
contrary to F 6j= 0 and L being consistent. And if md(0 )  n then either
 ! 0 2 K, which is impossible, since (M  ) 6j=  ! 0 , or  ! :0 2 K,
from which 0 ! : 2 K and so : 2 L, contrary to  being L-consistent.

W

2

Logics with 23-axioms Another result, connecting FMP of logics with
the distribution of 2 and 3 over their axioms, is based on the following

LEMMA 1.50 For any ' and , 3' $ 3 2 S5 i 23' $ 23 2 K4.

Proof Suppose 23' ! 23 62 K4. Then there is a nite model M,

based on a transitive frame, and a point x in it such that x j= 23' and
x 6j= 23. It follows from the former that every nal cluster accessible
from x, if any, is non-degenerate and contains a point where ' is true. The
latter means that x sees a nal cluster C at all points of which  is false.
Now, taking the generated submodel of M based on C , we obtain a model
for S5 refuting 3' ! 3. The rest is obvious, since 3p $ 32p is in S5
and K4 S5.
2
Formulas in which every occurrence of a variable is in the scope of a
modality 23 will be called 23-formulas.
THEOREM 1.51 (Rybakov 1978) If a logic L 2 NExtK4 is decidable (or
has FMP) and  is a 23-formula then L   is also decidable (has FMP).

Proof Let  = 0(231 : : :  23n), for some formula 0(q1  : : :  qn). If

'(p1  : : :  pm ) 2 L   then there exists a derivation of ' in L   in which
substitution instances of  contain no variables di erent from p1  : : :  pm.
Each of these instances has the form 0 (2301  : : :  230n), where every 0i is
some substitution instance of i containing only p1  : : :  pm . By Lemma 1.50
and in view of the local tabularity of S5 (it is of depth 1), there are nitely

ADVANCED MODAL LOGIC

45

many pairwise non-equivalent in K4 substitution instances of 23i of that
sort (the reader can easily estimate the number of them). So there exist
only nitely many pairwise non-equivalent in K4 substitution instances of
 containing p1  : : :  pm, say 1  : : :  k , and we can e ectively construct
them. Then, by the Deduction Theorem,

' 2 L   i 1  : : :  k `L ' i 2+ (1 ^ : : : ^ k ) ! ' 2 L
and so L   is decidable (or has FMP) whenever L is decidable (has FMP).
2
It should be noted that by adding to L with FMP innitely many 23formulas we can construct an incomplete logic. For a concrete example see
Rybakov 1977]. By adding a variable free formula to a logic in NExtK with
FMP one can get a logic without FMP. However, K  ', ' variable free,
has FMP, as can be easily shown by the standard ltration through the set
Sub'  Sub, where  62 K  '. Innitely many variable free formulas can
axiomatize a normal extension of K4 without FMP (for a concrete example
see Chagrov and Zakharyaschev 1997]).

1.8 Subframe and conal subframe logics

A very useful source of information for investigating various properties of
logics in NExtK4 is their canonical axioms. Notice, for instance, that the
canonical axioms of all logics in Table 2, save A and K4nm , contain no
closed domains. Canonical and negation free canonical formulas of the form
(F) and (F ?) are called subframe and conal subframe formulas, respectively, and logics in NExtK4 axiomatizable by them are called subframe and
conal subframe logics. The classes of such logics will be denoted by SF
and CSF . Subframe and conal subframe logics in NExtK4 were studied
by Fine 1985] and Zakharyaschev 1984, 1988, 1996].
THEOREM 1.52 All logics in SF and CSF have FMP.

Proof Suppose L = K4 f(Fi ?) : i 2 I g and ' 62 L. By Theorem 1.44,

without loss of generality we may assume that ' is a canonical formula,
say, (F D ?). Now consider two cases. (1) For no i 2 I , F is conally
subreducible to Fi . Then F j= L, F 6j= (F D ?), and we are done. (2) F
is conally subreducible to (Fi  ?), for some i 2 I . In this case we have
(F D ?) 2 K4  (Fi  ?) L, which is a contradiction. Indeed, suppose
G 6j= (F D ?). Then there is a conal subreduction of G to F. And since
the composition of (conal) subreductions is again a (conal) subreduction,
G is conally subreducible to Fi , which means that G 6j= (Fi  ?). Subframe
logics are treated analogously.
2

46

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

The names \subframe logic" and \conal subframe logic" are explained
by the following frame-theoretic characterization of these logics. A subframe
G = hV S Qi of a frame F is called conal if V " V # in F. Say that a class
C of frames is closed under (conal) subframes if every (conal) subframe
of F is in C whenever F 2 C .
THEOREM 1.53 L 2 NExtK4 is a (conal) subframe logic i it is characterized by a class of frames that is closed under (conal) subframes.

Proof Suppose L 2 CSF . We show that the class of all frames for L is

closed under conal subframes. Let G j= L and H be a conal subframe
of G. If H 6j= (F ?), for some (F ?) 2 L, then (since G is conally
subreducible to H) G 6j= (F ?), which is a contradiction. So H j= L.
Now suppose that L is characterized by some class of frames C closed
under conal subframes. We show that L = L0 , where

L0 = K4  f(F ?) : F 6j= Lg:
If F is a nite rooted frame and F 6j= L then (F ?) 2 L, for otherwise
G 6j= (F ?) for some G 2 C , and hence there is a conal subframe H of
G which is reducible to F but H 2 C and so, by the Reduction Theorem,
F is a frame for L, which is a contradiction. Thus, L0 L. To prove the
converse, suppose (F D ?) 2 L. Then F 6j= L, and hence (F ?) 2 L0,
from which (F D ?) 2 L0 .
Subframe logics are considered in the same way.
2
It follows in particular that SF  CSF (K4:1 and K4:2 are conal
subframe logics but not subframe ones). One can easily show also that
CSF is a complete sublattice of NExtK4 and SF a complete sublattice of
CSF .

EXAMPLE 1.54 Every normal extension of S4:3 is axiomatizable by canonical formulas which are based on chains of non-degenerate clusters and so
have no closed domains. Therefore, NExtS4:3  CSF .
The classes SF and CSF ; SF contain a continuum of logics. And
yet, unlike NExtK or NExtK4, their structure and their logics are not so
complex. For instance, it is not hard to see that every logic in CSF is
uniquely axiomatizable by an independent set of conal subframe formulas
and so these formulas form an axiomatic basis for CSF .
The concept of subframe logic was extended in Wolter 1993] to the class
NExtK by taking the frame-theoretic characterization of Theorem 1.53 as
the denition. Namely, we say that L 2 NExtK is a subframe logic if the
class of frames for L is closed under subframes. In other words, subframe

ADVANCED MODAL LOGIC

47

logics are precisely those logics whose axioms \do not force the existence of
points". For example, K, KB, K5, T, and Altn are subframe logics. To
give a syntactic characterization of subframe logics we require the following
formulas.
For a formula ' and a variable p not occurring in ', dene a formula 'p
inductively by taking

qp
= q ^ p q an atom
( $ )p = p $ p  for $ 2 f^ _ !g
(2)p
= 2(p ! p ) ^ p
and put 'sf = p ! 'p .
LEMMA 1.55 For any frame F, F j= 'sf i ' is valid in all subframes of
F.

Proof It suces to notice that if M is a model based on F, M0 a model
based on the subframe of F induced by fy : (M y) j= pg and (M x) j= q i
(M0  x) j= q, for all variables q, then (M x) j= 'p i (M0  x) j= '.
2

PROPOSITION 1.56 The following conditions are equivalent for any modal
logic L:
(i) L is a subframe logic
(ii) L = K  f'sf : ' 2 ;g, for some set of formulas ;
(iii) L is characterized by a class of frames closed under subframes.

Proof The implication (i) ) (iii) is trivial (iii) ) (ii) and (ii) ) (i) are
consequences of Lemma 1.55.

2

It follows that the class of subframe logics forms a complete sublattice of
NExtK. However, not all of them have FMP and even are Kripke complete.
EXAMPLE 1.57 Let L be the logic of the frame F constructed in Example 1.7. Since every rooted subframe G of F is isomorphic to a generated
subframe of F, L is a subframe logic. We show that L has the same Kripke
frames as GL:3. Suppose G is a rooted Kripke frame for GL:3 refuting
' 2 L. Then clearly G contains a nite subframe H refuting '. Since H is
a nite chain of irreexive points, it is isomorphic to a generated subframe
of F, contrary to F 6j= '. Thus G j= L. Conversely, suppose G is a Kripke
frame for L. Then G is irreexive. For otherwise G refutes the formula
' = 22 (2p ! p) ^ 2(2p ! p) ! 2p, which is valid in F. Let us show
now that G is transitive. Suppose otherwise. Then G refutes the formula
2p ! 2(2p _ (2q ! q)), which is valid in F because ! is a reexive point.
Finally, since G j= ', G is Noetherian and since F is of width 1, we may

48

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

conclude that G j= GL:3. It follows that the subframe logic L is Kripke
incomplete. Indeed, it shares the same class of Kripke frames with GL:3
but 2p ! 22p 2 GL:3 ; L.
The following theorem provides a frame-theoretic characterization of those
complete subframe logics in NExtK that are elementary, D{persistent and
strongly complete. Say that a logic L has the nite embedding property if
a Kripke frame F validates L whenever all nite subframes of F are frames
for L.
THEOREM 1.58 (Fine 1985) For each Kripke complete subframe logic L
the following conditions are equivalent:
(i) L is universal9
(ii) L is elementary
(iii) L is D{persistent
(iv) L is strongly Kripke complete
(v) L has the nite embedding property.

Proof The implications (i) ) (ii) and (iii) ) (iv) are trivial (ii) ) (iii)

follows from Fine's 1975b] Theorem formulated in Section 1.3 and (v) )
(i) from Tarski 1954]. Thus it remains to show that (iv) ) (v). Suppose
F is a Kripke frame with root r such that F 6j= L but all nite subframes
of F validate L. Then it is readily checked that all nite subsets of ; =
fpr g  2<! F are L-consistent. Hence the whole set ; is L-consistent. On
the other hand, similarly to the proof of Lemma 1.13 one can show that ; is
satisable in a Kripke frame i the frame is subreducible to F. So ; cannot
be satised in a Kripke frame for L and L is not strongly complete.
2
A similar criterion for the conal subframe logics in NExtK4 can be
found in Zakharyaschev 1996]. Note, however, that they are not in general
universal and certainly do not have the nite embedding property, but (ii),
(iii) and (iv) are still equivalent.
PROPOSITION 1.59 Every subframe logic L 2 NExtAltn has FMP.

Proof Suppose ' 62 L. By Theorem 1.22, there is a Kripke frame F for L

refuting ' at a point x. Denote by X the set of points in F accessible from
x by  md(') steps. Clearly, X is nite and the subframe of F induced by
X validates L and refutes '.
2
To understand the place of incomplete logics in the lattice of subframe
logics we call a subframe logic L strictly sf-complete if it is Kripke complete
9 I.e., universal is the class of Kripke frames for L considered as models of the rst
order language with R and =.

ADVANCED MODAL LOGIC

49



6

2



1

.
..
G 
(b)

6

6

6

F 0
(a)

Figure 5.
and no other subframe logic has the same Kripke frames as L. Example 1.57
shows that GL:3 is not strictly sf-complete. However, the logics T, S4 and
Grz turn out to be strictly sf-complete. The following result claries the
situation. It is proved by applying the splitting technique to lattices of
subframe logics.
THEOREM 1.60 A subframe logic L containing K4 is strictly sf-complete
i L 6 GL:3. All subframe logics in NExtAltn are strictly sf-complete.
A subframe logic is tabular i there are only nitely many subframe logics
containing it.

1.9 More su cient conditions of FMP
As follows from Theorem 1.52, a logic in NExtK4 does not have FMP only
if at least one of its canonical axioms contains closed domains. We illustrate
their role by a simple example.

EXAMPLE 1.61 Consider the logic L = K4:3  ] (F ?) and the formula
(F ?), where F is the frame depicted in Fig. 5 (a). The frame G in
Fig. 5 (b) separates (F ?) from L. Indeed, F is a conal subframe of G
and so G 6j= (F ?). To show that G j= ] (F ?), suppose f is a conal
subreduction of G to F. Then f ;1(1) contains only one point, say x f ;1(0)
also contains only one point, namely the root of G. So the innite set of
points between x and the root is outside domf , which means that f does
not satisfy (CDC) for ff1gg. On the other hand, if H is a nite refutation
frame of width 1 for (F ?) then H contains a generated subframe reducible
to F, from which H 6j= L. Thus, L fails to have FMP. In the same manner
the reader can prove that A in Table 2 does not have FMP either.
We show now two methods developed in Zakharyaschev 1997a] for establishing FMP of logics whose canonical axioms contain closed domains.
One of them uses the following lemma, which is an immediate consequence
of the refutability criterion for the canonical formulas.

50

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

LEMMA 1.62 Suppose (F D) and (G E) ((F D ?) and (G E ?))
are canonical formulas such that there is a (conal) subreduction f of G
to F satisfying (CDC) for D and an antichain e domf " is in E whenever
f (e") = d" for some d 2 D. Then (G E) 2 K4  (F D) (respectively,
(G E ?) 2 K4  (F D ?)).
THEOREM 1.63 L = K4  f(Fi  Di  ?) : i 2 I g  f(Fj  Dj ) : j 2 J g has
FMP provided that either all frames Fi , for i 2 I  J , are irreexive or all
of them are reexive.

Proof Suppose all Fi are irreexive and (G E ?) is an arbitrary canonical formula. We construct from G a new nite frame H by inserting into it
new reexive points. Namely, suppose e is an antichain in G such that e 62 E.
Suppose also that C1  : : :  Cn are all clusters in G such that e Ci " and
e \ Ci = , for i = 1 : : :  n, but no successor of Ci possesses this property.
Then we insert in G new reexive points x1  : : :  xn so that each xi could
see only the points in e and their successors and could be seen only from the
points in Ci and their predecessors. The same we simultaneously do for all
antichains e in G of that sort. The resulting frame is denoted by H. Since
no new point was inserted just below an antichain in E, H 6j= (G E ?).
Suppose now that (G E ?) 62 L and show that H j= L. If this is not so
then either H 6j= (Fi  Di  ?), for some i 2 I , or H 6j= (Fj  Dj ), for some
j 2 J . We consider only the former case, since the latter one is treated
similarly. Thus, we have a conal subreduction f of H to Fi satisfying
(CDC) for Di . Since Fi is irreexive, no point that was added to G is in
domf . So f may be regarded as a conal subreduction of G to Fi satisfying
(CDC) for Di . We clearly may assume also that the subframe of G generated
by domf is rooted. Let e be an antichain in G belonging to domf " and such
that f (e") = d" for some d 2 Di . If e 62 E then there is a reexive point
x in H such that x 2 domf " and x sees only e" and, of course, itself. But
then f (x") = f (e") = d" and so, by (CDC), x 2 domf , which is impossible.
Therefore, e 2 E and so, by Lemma 1.62, (G E ?) 2 L, contrary to our
assumption.
In the case of reexive frames irreexive points are inserted.
2
EXAMPLE 1.64 According to Theorem 1.63, the logic
1 2
K 
A

L = K4  ( A  ff1g f1 2gg)
has FMP. However, Artemov's logic A = L  GL does not enjoy this
property. So FMP is not in general preserved under sums of logics.

ADVANCED MODAL LOGIC

51

The scope of the method of inserting points is not bounded only by canonical axioms associated with homogeneous (irreexive or reexive) frames. It
can be applied, for instance, to normal extensions of K4 with modal reduction principles, i.e., formulas of the form M p ! N p, where M and N are
strings of 2 and 3 (for rst order equivalents of modal reduction principles
see van Benthem 1976]). One can show that each such logic is either of
nite depth, or can be axiomatized by 23-formulas and canonical formulas
based upon almost homogeneous frames (containing at most one reexive
point), for which the method works as well. So we have
THEOREM 1.65 All logics in NExtK4 axiomatizable by modal reduction
principles have FMP and are decidable.
One of the most interesting open problems in completeness theory of
modal logic is to prove an analogous theorem for logics in NExtK or to
construct a counter-example. It is unknown, in particular, whether the
logics K  2m p ! 2n p have FMP the same concerns the logics K  tran .
The second method of proving FMP uses the more conventional technique
of removing points. Suppose that L = K4  f(Gi  Di  ?) : i 2 I g and
 = (H E ?) 62 L. Then there exists a frame F for L such that F 6j= ,
i.e., there is a conal subreduction h of F to H satisfying (CDC) for E.
Construct the countermodel M = hF Vi for  as it was done in Section 1.6.
Without loss of generality we may assume that domh" = domh# = F and
that F is generated by the sets V(pi ), pi a variable in .
Actually, the step-wise renement procedure with deleting points having
Sub-equivalent successors, used in the proof of Theorem 1.42, establishes
FMP of L when all Di are empty, i.e., L is a conal subframe logic. To
tune it for L with non-empty Di , we should follow a subtler strategy of
deleting points, preserving those that are \responsible" for validating the
axioms of L. Suppose we have already constructed a model M0n = hF0n  V0n i
by \folding up" n ; 1-cyclic sets into clusters of depth n (we use the same
notations as in the proof of Theorem 1.42). Now we throw away points of
two sorts.
First, for every proper cluster C of depth n such that some x 2 C has
a Sub-equivalent successor of depth < n, we remove from C all points
except x. Second, call a point x of depth > n redundant in M0n if it has
a Sub-equivalent successor of depth  n and, for every i 2 I and every
conal subreduction g of (F0n )n to the subframe of Gi generated by some
d 2 Di such that d g(x") and g satises (CDC) for Di , there is a point
y 2 x " of depth  n such that g(y ") = d". Let X be the maximal
set of redundant points in M0n which is upward closed in (Wn0 )>n . We
dene Mn+1 = hFn+1  Vn+1 i as the submodel of M0n resulting from it by
removing all points in X as well. Since all deleted points have Subequivalent successors, Mn+1 6j= . And since we keep in Fn+1 points which

52

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

violate (CDC) for Di of possible conal subreductions to Gi , Fn+1 j= L.
So FMP of L will be established if we manage to prove that this process
eventually terminates.
2
1 6
 
K 
A

EXAMPLE 1.66 Let L = S4  (G ff1 2gg ?), where G is A , and
assume that our \algorithm", when being applied to F,  and L, works
innitely long. Then the frame F! = hW!  R! i, where

W! =

 W i R! =  R i Fi = hWi Ri Pii 


0<i<!

i



0<i<!

i

is of innite depth. By Konig's Lemma, there is an innite descending
chain : : : xi R! xi;1 : : : R! x2 R! x1 in F! such that xi is of depth i. Since
there are only nitely many pairwise non-Sub-equivalent points, there
must be some n > 0 such that, for every k n, each point in C (xk ) has a
1
Sub-equivalent successor in F<k
k . And since F1 is nite, there is m n
starting from which all xi see the same points of depth 1. Let us consider
now Fm and ask why points in the m-cyclic set X , folded at step m + 1
into C (xm+1 ), were not removed at step m. X is upward closed in Wm>m
and every point in it has a Sub-equivalent successor in Fmm . So the only
reason for keeping some x 2 X is that Fmm is conally subreducible to G1 ,
x sees inverse images of both points in G1 but none of its successors in
Fmm does. By the conality condition, these inverse images can be taken
from F1 1 . But then they are also seen from xm , which is a contradiction.
Thus sooner or later our algorithm will construct a nite frame separating
L from , which proves that L has FMP.
The reason why we succeeded in this example is that inverse images of
points in the closed domain f1 2g can be found at a xed nite depth in
F! , and so points violating (CDC) for it can also be found at nite depth
(that was not the case in Example 1.61). The following denitions describe
a big family of frames and closed domains of that sort.
A point x in a frame G is called a focus of an antichain a in G if x 62 a
and x" = fxg  a". Suppose G is a nite frame and D a set of antichains
in G. Dene by induction on n notions of n-stable point in G (relative to
D) and n-stable antichain in D. A point x is 1-stable in G i either x is of
depth 1 in G or the cluster C (x) is proper. A point x is n + 1-stable in G
(relative to D) i it is not m-stable, for any m  n, and either there is an
n-stable point in G (relative to D) which is not seen from x or x is a focus
of an antichain in D containing an n ; 1-stable point and no n-stable point.
And we say an antichain d in D is n-stable i it contains an n-stable point

ADVANCED MODAL LOGIC

1

1

6
K ;
A
6
A
;
3  A 2
6
K ;
A
6
A AA
;
5  A 4
6
KA ;
A

A 6
;
A
7  A 6



(a)

1

1

6
AK  6
A 
2  A  2
6
AK A 6
A 
3  A A 3
6
AKA A 6

4  A A 4



(b)

1 1

53

1

6
I
@
@
;
I;
6
@;
;
@
;
2  2  @ 2
6
I
@
@
;
I;
6
@;
;@ ;@
3  3  3
6
I
@
@
;
I;
6
@;
;
@
;
4  4  @ 4



(c)

1

1

6
I
@
6
;
@;
;
3  @ 3
6
I
@
6
;
@;
;
5  @ 5
6
I
@
6
;
@;
;
7  @ 7



(d)

Figure 6.
in the subframe G0 of G generated by d (relative to D) and no m-stable
point in G0 (relative to D), for m > n. A point or an antichain is stable if
it is n-stable for some n. It should be clear that if a point in an antichain
is stable then the rest points in the antichain are also stable.
EXAMPLE 1.67 (1) Suppose G is a nite rooted generated subframe of one
of the frames shown in Fig. 6 (a){(c). Then, regardless of D, each point
in G di erent from its root is n-stable, where n is the number located near
the point. Every antichain d in G, containing at least two points, is also
n-stable, with n being the maximal degree of stability of points in d.
(2) If G is a rooted generated subframe of the frame depicted in Fig. 6
(d) and D is the set of all two-point antichains in G then every point in G is
n-stable (relative to D), where n stays near the point. However, for D = 
no point in G, save those of depth 1, is stable.
(3) If G is a nite tree of clusters then every antichain in G, di erent from
a non-nal singleton, is either 1- or 2-stable in G regardless of D. Every
antichain containing a point x with proper C (x) is 1- or 2-stable as well,
whatever G and D are.
(4) Every antichain is stable in every irreexive frame G relative to the
set D] of all antichains in G. However, this is not so if G contains reexive
points (for reexive singletons are open domains and do not belong to D] ).
The sucient condition of FMP below is proved by arguments that are
similar to those we used in Example 1.66.
THEOREM 1.68 If L = K4 f(Gi  Di  ?) : i 2 I g and there is d > 0 such
that, for any i 2 I , every closed domain d 2 Di is n-stable in Gi (relative
to Di ), for some n  d, then L has FMP.
Example 1.67 shows many applications of this condition. Moreover, using
it one can prove the following

54

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 1.69 Every normal extension of S4 with a formula in one variable has FMP and is decidable.
Note that, as was shown by Shehtman 1980], a formula in two variables
or an innite set of one-variable formulas can axiomatize logics in NExtS4
without FMP (and even Kripke incomplete).

1.10 The reduction method
That a logic does not have FMP (or is Kripke incomplete) is not yet an
evidence of its undecidability: it is enough to recall that the majority of
decidability results for classical theories was proved without using any analogues of the nite model property (see e.g. Rabin 1977], Ershov 1980]).
The rst example of a decidable nitely axiomatizable modal logic without
FMP was constructed by Gabbay 1971].
It seems unlikely that the methods of classical model theory can be applied directly for proving the decidability of propositional modal logics.
However, sometimes it is possible to reduce the decision problem for a given
modal logic L to that for a knowingly decidable rst or higher order theory
whose language is expressive enough for describing the structure of frames
characterizing L. The most popular tools used for this purpose are Buchi's
1962] Theorem on the decidability of the weak monadic second order theory
of the successor function on natural numbers and Rabin's 1969] Tree Theorem. Below we illustrate the use of Rabin's Theorem following Gabbay
1975] and Cresswell 1984].
Let ! be the set of all nite sequences of natural numbers and % the
lexicographic order on it. For x 2 ! and i < !, put ri (x) = x i, where
denotes the usual concatenation operation. Besides, dene the following
predicates <i on ! , for 0  i  2,

x <i y i y = x (3n + i) for some n < !:
It follows from Rabin 1969] that the monadic second order theory S!S
of the model h!  fri : i < !g f<i: 0  i  2g % i ( denotes the empty
sequence) is decidable.
The theory S!S has a very strong expressive power which makes it possible to e ectively describe semantical denitions of many modal (as well as
some other) logics and thereby prove their decidability. In this way Gabbay
1975] established the decidability of, for instance,

K  2m3p ! 3p K  3m2p ! 2p
K  2mp ! 3np K  3mp ! 2np:

ADVANCED MODAL LOGIC

55

By Sahlqvist's Theorem, all these logics are Kripke complete however, we
do not know whether they have FMP. General frames can also be described
by means of S!S.
EXAMPLE 1.70 The frame F = hW R P i constructed in Example 1.7 can
be represented in the language of S!S as follows. Let us encode each n < !
by the sequence h3ni, while ! and ! + 1 by r1 () and r2 (), respectively.
Then we have
x 2 W i  <0 x _ x = r1 () _ x = r2 ()
xRy i ( <0 x ^  <0 y ^ y % x ^ x 6= y) _
(x = r1 () ^  <0 y) _ x = y = r1 () _
(x = r2 () ^ y = r1 ())
X 2 P i 8x (x 2 X ! x 2 W ) ^ ((Fin(X ) ^ r1 () 2= X ) _
8Y (8y (y 2 Y $ (y 2 W ^ y 2= X )) ! Fin(Y ) ^ r1 () 2= Y ))
where x = y means x % y ^ y % x and
Fin(X ) = 9x8y (y 2 X ! y % x):
It follows that the logic LogF is decidable. Indeed, for every formula
'(p1  : : :  pn ), we have ' 2 LogF i the second order formula
8x8X1 : : :  Xn (X1 2 P ^ : : : ^ Xn 2 P ^ x 2 W ! ST ('(X1  : : :  Xn )))
belongs to S!S. Here ST ('(X1  : : :  Xn )), the standard translation of ', is
dened inductively in the following way (see also Correspondence Theory):
ST (X ) = x 2 X ST (?) = ?
ST (X $ Y ) = ST (X ) $ ST (Y ) for $ 2 f^ _ !g
ST (2X ) = 8y (xRy ! ST (X )fy=xg):
Recall that, as was shown in Example 1.57, LogF is Kripke incomplete.
Also, it is not hard to nd examples of applications of this technique
for proving the decidability of nitely axiomatizable quasi-normal unimodal
and normal polymodal (in particular, tense) logics which do not have Kripke
frames at all perhaps, the simplest one is Solovay's logic S.
Sobolev 1977a] found another way of proving decidability by applying
methods of automata theory on innite sequences. Using the results of
Buchi and Siefkes 1973] he showed that all nitely axiomatizable superintuitionistic logics of nite width (see Section 3.4) containing the formula
(((p ! q) ! p) ! p) _ (((q ! p) ! q) ! q):

56

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

are decidable. By the preservation theorem of Section 3.3, this result can
be transferred to the corresponding extensions of S4.
If a logic is known to be complete with respect to a suitable class of
frames, the methods discussed above are usually applicable to it in a rather
straightforward manner. A relative disadvantage of this approach is that the
resulting decision algorithms inherit the extremely high complexity of the
decision algorithms for S!S or other \rich theories" used to prove decidability. On the other hand, the logic S, for instance, turns out to be decidable
by an algorithm of the same complexity as that for GL (see Example 1.75),
in particular, the derivability problem in S is PSPACE -complete. The
logic of the frame F in Example 1.7 is \almost trivial"|it is polynomially
equivalent to classical propositional logic, which follows from the fact that
every formula ' refutable by F can be also refuted in F under a valuation giving the same truth-value to all variables in ' at all points i such
that jSub'j < i < ! (see Section 4.6). Actually, this sort of decidability
proofs (ignoring \inessential" parts of innite frames) was used already by
Kuznetsov and Gerchiu 1970] for studying some superintuitionistic logics.
Recently more general semantical methods of obtaining decidability results without turning to \rich theories" have been developed. We demonstrate them in the next section by establishing the decidability of all nitely
axiomatizable logics in NExtK4:3, which according to Example 1.61 do not
in general have FMP. We show, however, that those logics are complete
with respect to recursively enumerable classes of recursive frames in which
the validity of formulas can be e ectively checked|it was this rather than
the niteness of frames that we used in the proof of Harrop's Theorem. In
Section 2.5 this result will be extended to linear tense logics which in general
are not even Kripke complete. Our presentation follows Zakharyaschev and
Alekseev 1995].

1.11 Logics containing K4:3
Each logic in L 2 NExtK4:3 is represented in the form
L = K4:3  f(Fi  Di  ?) : i 2 I g
where all Fi are chains of clusters. So our decidability problem reduces to
nding an algorithm which, given such a representation with nite I and
a canonical formula (F D ?) built on a chain of clusters F, could decide
whether (F D ?) 2 L. Recall also that, by Fine's 1974c] Theorem, logics
of width 1 are characterized by Kripke frames having the form of Noetherian
chains of clusters.

ADVANCED MODAL LOGIC

57

LEMMA 1.71 For any Noetherian chain of clusters G and any canonical
formula (F D ?), G 6j= (F D ?) i there is an injective10 conal subreduction g of G to F satisfying (CDC) for D.

Proof If G 6j= (F D ?) then there is a conal subreduction f of G to

F satisfying (CDC) for D. Clearly, f ;1(x) is a singleton if x is irreexive.
Suppose now that x is a reexive point in F. Since G contains no innite
ascending chains, f ;1 (x) has a nite cover and so there is a reexive point
ux 2 f ;1 (x) such that f ;1 (x) ux#. Fix such a ux for each reexive x and
dene a partial map g by taking
8< f (y) if either f (y) is irreexive or
g(y) = :
f (y) is reexive and y = uf (y)
undened otherwise.
One can readily check that g is the injective conal subreduction we need.
The converse is trivial.
2
Roughly, every Noetherian chain of clusters refuting (F D ?) results
from F by inserting some Noetherian chains of clusters just below clusters
C (x) in F such that fxg 62 D. We show now that if (F D ?) is not in
L 2 NExtK4:3 then it can be separated from L by a frame constructed
from F by inserting in open domains between its adjacent clusters either
nite descending chains of irreexive points possibly ending with a reexive
one or innite descending chains of irreexive points.
Let C (x0 ) : : :  C (xn ) be all distinct clusters in F ordered in such a way
that C (x0 )  C (x1 )#  : : :  C (xn )#. Say that an n-tuple t = h1  : : :  n i
is a type for (F D ?) if either i = m or i = m+, for some m < !, or
i = !, with i = 0 if fxi g 2 D. Given a type t = h1  : : :  n i for (F D ?),
we dene the t-extension of F to be the frame G that is obtained from F
by inserting between each pair C (xi;1 ), C (xi ) either a descending chain of
m irreexive points, if i = m < !, or a descending chain of m + 1 points
of which only the last (lowest) one is reexive, if i = m+, or an innite
descending chain of irreexive points, if i = !. It should be clear that
G 6j= (F D ?).
LEMMA 1.72 If L 2 NExtK4:3 and (F D ?) 62 L then (F D ?) is
separated from L by the t-extension of F, for some type t for (F D ?).
Proof By Lemma 1.71, we have a Noetherian chain of clusters G for L
and an injective conal subreduction f of G to F satisfying (CDC) for D.
By the Generation Theorem, we may assume that f maps the root of G to
the root of F. Let G0 be the subframe of G obtained by removing from G
10

That is g(x) 6= g(y), for every distinct x y 2 domg.

58

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

all those points that are not in domf but belong to clusters containing some
points in domf . The very same map f is an injective conal subreduction
of G0 to F satisfying (CDC) for D, and so G0 6j= (F D ?). Since G0 is a
reduct of G, G0 j= L.
Let C (x0 ) : : :  C (xn ) be all distinct clusters in G0 such that
n

domf = C (xi ) C (x )  C (x )#  : : :  C (xn )#:
i=0

0

1

By induction on i we dene a sequence of frames G0  : : :  Gn such that
(a) f is an injective conal subreduction of Gi to F satisfying (CDC) for
D, (b) between C (xi;1 ) and C (xi ) the frame Gi contains either a nite
descending chain of irreexive points possibly ending with a reexive one
or an innite descending chain of irreexive points, and (c) Gi j= L.
Suppose Gi;1 has been already constructed and Ci is the chain of clusters
located between C (xi;1 ) and C (xi ). Three cases are possible. (1) Ci is a
nite chain of irreexive points. Then we put Gi = Gi;1 . (2) Ci contains
a non-degenerate cluster C (x) having nitely many distinct successors in
Ci and all of them are irreexive. Then Gi results from Gi;1 by removing
from Ci all points save x and those successors. Gi is a reduct of Gi;1
and so conditions (a){(c) are satised. (3) Suppose (1) and (2) do not
hold. Then Ci contains an innite descending chain Y of irreexive points
accessible from all other points in Ci . In this case Gi is obtained from Gi;1
by removing all points in Ci save those in Y . Clearly, Gi satises (a) and
(b). To prove (c) suppose Gi 6j= (H E ?) for some (H E ?) 2 L. Then
there is an injective conal subreduction g of Gi to H satisfying (CDC) for
E. Consider g as a conal subreduction of Gi;1 to H and show that it also
satises (CDC) for E. Indeed, (CDC) could be violated only by a point in
z 2 Ci ; Y such that g(z ") = w", for some fwg 2 E. Since g;1 (w) is a
singleton and Y z", there is y 2 Y such that g(y") = w" and y 62 domg,
contrary to g satisfying (CDC) for E as a subreduction of Gi to H.
2
Thus, a frame separating (F D ?) 62 L from L 2 NExtK4:3 can be
found in the recursively enumerable class of t-extensions of F, t being a
type for (F D ?). Moreover, given a formula (H E ?) and a type t
for (F D ?), one can e ectively check whether (H E ?) is valid in the
t-extension of F. Indeed, let k be the number of irreexive points in H,
t = h1  : : :  n i, and G the t-extension of F. Construct a conal subframe
Gk of G by \cutting o " the innite descending chains inserted in F (if any)
just below their k + 1th points, and let X be the set of all these k + 1th
points. Clearly, Gk is nite. It is now an easy exercise to prove the following
LEMMA 1.73 G 6j= (H E ?) i there is an injective conal subreduction
f of Gk to H satisfying (CDC) for E and such that X \ domf = .

ADVANCED MODAL LOGIC

59

0

6

1



 
F

6

1

2
..
.
G !


;
;
I
@
@;

0

Figure 7.
As a consequence we obtain
THEOREM 1.74 All nitely axiomatizable normal extensions of K4:3 are
decidable.

1.12 Quasi-normal modal logics
All logics we have considered so far were normal, i.e., closed under the rule
of necessitation '=2'. McKinsey and Tarski 1948] noticed, however, that
by adding to S4 the McKinsey axiom ma = 23p ! 32p and taking
the closure under modus ponens and substitution we obtain a logic|let us
denote it by S4:10 |which is not normal in that sense. To understand why
this is so, consider the frame F shown in Fig. 7. One can easily construct
a model on F such that 0 6j= 2ma (0 sees a nal proper cluster). On the
other hand, ma and all its substitution instances are true at 0 (0 sees a
nal simple cluster), from which S4:10 f' : 0 j= 'g and so 2ma 62 S4:10 .
A set of modal formulas containing K and closed under modus ponens
and substitution was called by Segerberg 1971] a quasi-normal logic. The
minimal quasi-normal extension of a logic L with formulas 'i , i 2 I , will be
denoted by L + f'i : i 2 I g (i.e., the operation + presupposes taking the
closure under modus ponens and substitution only). ExtL is the class of all
quasi-normal logics above L. It is easy to see that a quasi-normal logic is
normal i it is closed under the congruence rule p $ q=2p $ 2q.
Quasi-normal logics, introduced originally as some abstract (though natural) generalization of normal ones, attracted modal logicians' attention
after Solovay 1976] constructed his provability logics GL and S. The former one treats 2 as \it is provable in Peano Arithmetic" and describes
those properties of Godel's provability predicate that are provable in PA it
is normal. The latter characterizes the properties of the provability predicate that are true in the standard arithmetic model, and in view of Godel's
Incompleteness Theorem it cannot be normal. (For a detailed discussion of
provability logic consult Modal Logic and Self-reference.) Solovay showed

60

in fact that

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

S = GL + 2p ! p:

At rst sight S may appear to be inconsistent: Lob's axiom requires frames
to be irreexive, while 2p ! p is refuted in them. And indeed, no Kripke
frame validates both these axioms (in particular no consistent extension of
S is normal).
Having the algebraic semantics for normal modal logics, it is fairly easy to
construct an adequate algebraic semantics for a consistent L 2 ExtK. Let
M be a normal logic contained in L (for instance the greatest one, which is
called the kernel of L) and AM its Tarski{Lindenbaum algebra (in Section
11 of Basic Modal Logic it was called the canonical modal algebra for M ).
The set
r = f']M : ' 2 Lg
is clearly a lter in AM . By the well known properties of the Tarski{
Lindenbaum algebras, we then obtain the following completeness result:
' 2 L i under every valuation in AM the value of ' belongs to r. Structures of the form hA ri, where A is a modal algebra and r a lter in A, are
known as modal matrices. Thus, every quasi-normal logic is characterized
by a suitable class of modal matrices. It is not hard to see that L is normal
i it is characterized by a class of modal matrices with unit lters.
Now, going over to the dual (Stone{Jonsson{Tarski representation) A+
of A in a modal matrix hA ri and taking r+ to be the set of ultralters in
A containing r, we arrive at the general frame A+ with the set of distinguished points (or actual worlds) r+ . A formula ' is regarded to be valid
in hA+  r+ i i under any valuation in A+ , ' is true at all points in r+ .
Taking into account the Generation Theorem, we can conclude that every quasi-normal modal logic is characterized by a suitable class of rooted
general frames in which the root is regarded to be the only actual world.
It follows in particular that, as was rst observed by McKinsey and Tarski
1948],
K4 + f2'i : i 2 I g = K4  f2'i : i 2 I g:
However, one cannot replace here K4 by K or T. Note also that as was
shown by Segerberg 1971], K, T and some other standard normal logics
are not nitely axiomatizable with modus ponens and substitution as the
only postulated inference rules. Duality theory between modal matrices and
frames with distinguished points can be developed along with duality theory
for normal logics (for details see Chagrov and Zakharyaschev 1997]). Kripke
frames with distinguished points were used for studying quasi-normal logics
by Segerberg 1971]. Modal matrices were considered by Blok and Kohler
1983] (under the name of ltered algebras), Chagrov 1985b], and Shum
1985].

ADVANCED MODAL LOGIC

61

EXAMPLE 1.75 Consider the (transitive) frame G = hV S Qi whose underlying Kripke frame is shown in Fig. 7 and Q consists of , V , all nite sets of natural numbers and the complements to them in the space
V (so ! 2 X 2 Q i there is n < ! such that m 2 X for all m n).
Since G is irreexive and Noetherian, it validates GL. Moreover, we have
hG !i j= 2p ! p for if under some valuation ! j= 2p then p must be true
at every point. It follows that G with actual world ! validates S. (The
reader can check that by making ! reexive we again obtain a frame for S.)
By inserting the \tail" G as in Fig. 7 into nite rooted frames for GL
below their roots and using the fact that GL has FMP, one can readily
show that, for every formula ',
'2Si
(2 ! ) ! ' 2 GL:

^

22Sub'

It follows in particular that S is decidable.
This example shows that the concepts of Kripke completeness and FMP
do not play so important role in the quasi-normal case: even simple logics
require innite general frames. One possible way to cope with them at
least in the transitive case is to extend the frame-theoretic language of the
canonical formulas to the class ExtK4.
Notice rst that the canonical formulas, introduced in Section 1.6, cannot
axiomatize all logics in ExtK4. Indeed, hG wi 6j= (F D ?) i there is a
conal subreduction f of G to F satisfying (CDC) for D and the following
actual world condition as well:
(AWC) f (w) is the root of F.
Now, consider the frame hG !i constructed in Example 1.75. Since each set
X 2 Q containing ! is innite and has a dead end, it is impossible to reduce
X to  or , and so hG !i validates all normal canonical formulas. On the
other hand, we clearly have hG !i 6j= Bn for every n 1. So the logics
K4BDn cannot be axiomatized by normal canonical formulas without the
postulated necessitation.
To get over this obstacle we have to modify the denition of subreduction
so that such sets as X above may be \reduced" at least to irreexive roots
of frames. Given a frame G = hV S Qi with an irreexive root u and a
frame F = hW R P i, we say a partial map f from W onto V is a quasisubreduction of F to G if it satises (R1) for all x y 2 domf such that
f (x) 6= u or f (y) 6= u, (R2) and (R3).11 Thus, we may map all points in
the frame G in Fig. 7 to , and this map will be a quasi-reduction of G to
 satisfying (AWC). Actually, every frame is quasi-reducible to .
11 Another possibility is to allow \reductions" of X to reexive points by relaxing (R2)
cf. Section 2.6.

62

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Now, given a nite frame F with an irreexive root a0 and a set D of
antichains in F, we dene the quasi-normal canonical formula  (F D ?)
as the result of deleting 2p0 from '0 in (F D ?) (which says that a0 is not
self-accessible) the quasi-normal negation free canonical formula  (F D)
is dened in exactly the same way, starting from (F D). It is not hard
to see that  (F D ?) (or  (F D)) is refuted in a frame hG wi i there
is a conal (respectively, plain) quasi-subreduction of G to F satisfying
(CDC) for D and (AWC). The following result is obtained by an obvious
generalization of the proof of Theorem 1.44 to frames with distinguished
points (for details see Zakharyaschev 1992]).
THEOREM 1.76 There is an algorithm which, given a modal (negation
free) formula ', constructs a nite set of normal and quasi-normal (negation free) canonical formulas such that K4 + ' = K4 + .
For example, S = K4 + () + (). Since frames for S4 are reexive,
we have
COROLLARY 1.77 There is an algorithm which, given a modal formula
', constructs a nite set of normal canonical formulas built on reexive
frames such that S4 + ' = S4 + .
As a consequence we obtain
THEOREM 1.78 (Segerberg 1975) ExtS4:3 = NExtS4:3.
Proof We must show that every logic L 2 ExtS4:3 is normal, i.e., ' 2 L
only if 2' 2 L, for every '. Suppose otherwise. Then by Corollary 1.77,
there exists (F D ?) 2 L such that 2(F D ?) 62 L. Let hG wi be a
frame validating L and refuting 2(F D ?). Since G j= S4:3, G is a chain
of non-degenerate clusters. And since it refutes (F D ?) there is a conal
subreduction f of G to F. It follows, in particular, that F is also a chain
of non-degenerate clusters and so D = . Let a be the root of F. Dene a
map g by taking
f (x)
if x 2 domf
g(x) = a
if x 2 f ;1(a)#; domf
undened otherwise.
It should be clear that g conally subreduces G to F and g(w) = a. Consequently, hG wi 6j= (F ?), which is a contradiction.
2
Let us now briey consider quasi-normal analogues of subframe and conal subframe logics in NExtK4. Those logics that can be represented in
the form
(K4  f(Fi ) : i 2 I g) + f(Fj ) : j 2 J g + f (Fk ) : k 2 K g

8<
:

ADVANCED MODAL LOGIC
A

A

A 
Fr1 A0

A


A

A 
F Au

A
A




A 

Fir A0
6
. 1
..
 ;2
6
 ;1

63
A
A



A 
Fir(!+1)A0
6

. 1
..
!

Figure 8.
are called (quasi-normal) subframe logics and those of the form
(K4  f(Fi  ?) : i 2 I g) + f(Fj  ?) : j 2 J g + f (Fk  ?) : k 2 K g
are called (quasi-normal) conal subframe logics. The classes of quasinormal subframe and conal subframe logics are denoted by QSF and
QCSF , respectively. The example of S shows that Theorem 1.52 cannot
be extended to QSF and QCSF . Yet one can show that all nitely axiomatizable logics in QSF and QCSF are decidable. We omit almost all proofs
and conne ourselves mainly to formulations of relevant results. For details
the reader is referred to Zakharyaschev 1996].
We use the following notation. For a frame F = hW Ri with irreexive
root u and 0 <  < !, Fir and Fr denote the frames obtained from F
by replacing u with the descending chains 0 : : :   ; 1 of irreexive and
reexive points, respectively Fir(!+1) = W(!+1)  R(ir!+1)  P(!+1) is the
frame that results from F by replacing u with the innite descending chain
0 1 : : : of irreexive points and then adding irreexive root !, with P(!+1)
containing all subsets of W ; fug, all nite subsets of natural numbers
f0 1 : : :g, all (nite) unions of these sets and all complements to them in
the space W(!+1) (see Fig. 8). Note that F is a quasi-reduct of every frame
of the form Fir , Fr or Fir(!+1) .
The following theorem characterizes the canonical formulas belonging to
logics in QSF and QCSF .
THEOREM 1.79 Suppose L is a subframe or conal subframe quasi-normal
logic. Then
(i) for every nite frame F with root u, (F D ?) 2 L i hF ui 6j= L
(ii) for every nite frame F with irreexive root u,  (F D ?) 2 L i
hF ui 6j= L, hFr1  0i 6j= L and Fir(!+1)  ! 6j= L.

D









E







D

E



Proof We prove only (() of (ii). Let G = hV S Qi refute  (F D ?) at

its root w and show that hG wi 6j= L. We have a conal quasi-subreduction

64

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

f of G to F such that f (w) = u. Consider the set U = f ;1 (u) 2 Q. Without
loss of generality we may assume that U = U #. There are three possible

cases.
Case 1. The point w is irreexive and fwg 2 Q. Then the restriction of
f to domf ; (U ;fwg) is a conal subreduction of G to F satisfying (AWC)
and so hG wi 6j= L.
Case 2. There is X U such that w 2 X 2 Q and, for every x 2 X ,
there exists y 2 X \ x". Then the restriction of f to domf ; (U ; X ) is a
conal subreduction of G to Fr1 satisfying (AWC) and so again hG wi 6j= L.
Case 3. If neither of the preceding cases holds then, for every X U
such that w 2 X 2 Q, the set DX = X ; X # of dead ends in X is a cover
for X , i.e., X DX #, and w 2 X ; DX 2 Q. Put
X0 = DU  : : :  Xn+1 = DU ;(X0 ::: Xn )  : : :  X! = U ; X :



<!

S

Each of these sets, save possibly X! , is an antichain of irreexive points
and belongs to Q. Besides, X  Xn# = n< ! X for every n <   !.
Therefore, the map g dened by
g(x) = f (x) ifif xx 22 VX ; U0    !
is a conal quasi-subreduction of G to Fir(!+1) satisfying (AWC).
Now using the fact that Fir(!+1)  ! 6j= L and that the composition of
(conal) (quasi-) subreductions is again a (conal) (quasi-) subreduction, it
is not hard to see that hG wi 6j= L.
2
COROLLARY 1.80 All subframe and conal subframe quasi-normal logics
above S4 have FMP.
EXAMPLE 1.81 As an illustration let us use Theorem 1.79 to characterize
those normal and quasi-normal canonical formulas that belong to S. Clearly,
either () or () is refuted at the root of every rooted Kripke frame. So all
normal canonical formulas are in S. Every quasi-normal formula  (F D ?)
associated with F containing a reexive point is also in S, since 2() is
refuted at the roots of F, Fr1 and Fir(!+1) . But no quasi-normal formula
 (F D ?) built on irreexive F belongs to S, because Fir(!+1) j= () and
Fir(!+1)  ! j= (), since f!g 62 P(!+1) . Notice that incidentally we have
proved the following completeness theorem for S.
THEOREM 1.82 S is characterized by the class

D

E





D



E







D

E

f Fir(!+1)  ! : F is a nite rooted irreexive frameg:


ADVANCED MODAL LOGIC

65

Theorem 1.79 reduces the decision problem for a logic L in QSF or
QCSF to the problem of verifying, given a nite frame F with root u,
whether hF ui, hFr1  0i and Fir(!+1)  ! refute an axiom of L. The two
former frames present no diculties: they are nite. As to the latter, it is
not hard to see that, for instance, Fir(!+1)  ! 6j=  (G ?) i Fir   ; 1 ,
for some   jGj, is conally quasi-subreducible to G. Thus we obtain

D

D

E

E



D

E



THEOREM 1.83 All nitely axiomatizable subframe and conal subframe
quasi-normal logics are decidable.
One can also give a frame-theoretic characterization of the classes QSF
and QCSF similar to Theorem 1.53. Let us say that a frame F with actual
world u is a (conal) subframe of a frame G with actual world w if F is a
(conal) subframe of G and u = w.
THEOREM 1.84 L is a (conal) subframe quasi-normal logic i L is characterized by a class of frames with actual worlds that is closed under (conal)
subframes.

1.13 Tabular logics

Every logic L having the nite model property can be represented as the intersection of some tabular logics, that is logics characterized by nite frames
(or models, algebras, matrices, etc.):

\

L = fLogF : F is a nite frame for Lg:
(It follows in particular that every fragment of L containing only those
formulas whose length does not exceed some xed n < ! is determined
by a nite frame for that reason logics with FMP are also called nitely
approximable.) In many respects tabular logics are very easy to deal with.
For instance, the key problem of recognizing whether a formula ' belongs
to a tabular L is trivially decided by the direct inspection of all possible
valuations of ''s variables in the nite frame characterizing L. That is
why the question \is it tabular?" is one of the rst items in the standard
\questionnaire" for every new logical system.
First results concerning the tabularity of modal logics were obtained by
Godel 1932] and Dugundji 1940] who showed that intuitionistic propositional logic and all Lewis' modal systems S1{S5 are not tabular. (Note that
using the same method Drabbe 1967] proved that the three non-normal
Lewis' systems S1{S3 cannot be characterized by a matrix with a nite
number of distinguished elements). For arbitrary logics in ExtK one can

66

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

easily prove the following syntactical criterion of tabularity, which uses the
formulas
n = :('1 ^ 3('2 ^ 3('3 ^ : : : ^ 3'n) : : :))

n =

^ :3m(3' ^ : : : ^ 3'n)

n;1

m=0

1

tabn = n ^ n

where 'i = p1 ^ : : : ^ pi;1 ^ :pi ^ pi+1 ^ : : : ^ pn .
THEOREM 1.85 L 2 ExtK is tabular i tabn 2 L, for some n < !.

Proof A frame F = hW Ri refutes n at a point x1 i a chain of length n

starts from x1 , and F refutes n at x1 i there is a chain x1 Rx2 R : : : Rxm
of length m < n such that xm is of branching n, i.e., xm Ry1  : : :  xm Ryn
for some distinct y1  : : :  yn . It follows that every rooted generated (by an
actual world) subframe of the canonical frame for L containing tabn has at
most 1 + (n ; 1) + : : : + (n ; 1)n;2 points.
2
As a consequence we immediately obtain

COROLLARY 1.86 Every tabular modal logic has nitely many extensions
and all of them are also tabular.
The next theorem follows from general algebraic results of Blok and
Kohler 1983] equally easy it can be proved using the characterization above.
THEOREM 1.87 Every tabular logic L 2 ExtK is nitely axiomatizable.

Proof According to Theorem 1.85, L is an extension of K + tabn, for some
n < !. By Corollary 1.86, we have a chain

K + tabn = L1  L2  : : :  Lk;1  Lk = L
of quasi-normal logics such that fL0 2 ExtK : Li  L0  Li+1 g = , for

every i = 1 : : :  k ;1. It remains to notice that if L0 is nitely axiomatizable,
L0  L00 and there is no logic located properly between L0 and L00 then L00
is also nitely axiomatizable (e.g. L00 = L0 + ', for any ' 2 L00 ; L0).
2
Theorem 1.12 provides us in fact with an algorithm to decide, given a
tabular logic L 2 NExtK4 and an arbitrary formula ', whether K4' = L.
Indeed, notice rst that we have

ADVANCED MODAL LOGIC

67

THEOREM 1.88 Each nitely axiomatizable logic L 2 NExtK4 of nite
depth is a nite union-splitting, i.e., can be represented in the form

L = K4  f] (Fi  ?) : i 2 I g
with nite I .

Proof Let L = K4  ' be a logic of depth n and let m be the number of
variables in '. We show that L coincides with the logic

L0 = K4  f] (G ?) : jGj 

X 2mcm(i) G 6j= 'g

n+1
i=1

(cm (i) was dened in Section 1.2). The inclusion L  L0 is obvious. Suppose
' 62 L0 . Then there is a rooted rened m-generated frame F for L0 refuting
'. Clearly, F is of depth  n, since otherwise ] (G ?) is an axiom of L0
for every rooted generated subframe G of F of depth n + 1 and so F 6j= L0,
which is a contradiction. But then ] (F ?) is an axiom of L0 , contrary to
our assumption.
2
Thus, all tabular logics in NExtK4 are nite union-splittings and so, by
Theorem 1.12, we obtain the following
THEOREM 1.89 Let L be a tabular logic in NExtK4.
(i) (Blok 1980c) L has nitely many immediate predecessors and they are
also tabular.
(ii) The axiomatizability problem for L above K4 is decidable.
For logics in NExtK this is not the case, witness Theorems 1.36 and 4.13.
The tabularity criterion of Theorem 1.85 is not e ective. Moreover, as
we shall see in Section 4.4, no e ective tabularity criterion exists in general.
However, if we restrict attention to suciently strong logics, e.g. to the
class NExtS4, the tabularity problem turns out to be decidable. The key
idea, proposed by Kuznetsov 1971], is to consider the so called pretabular
logics.
A logic L 2 (N)ExtL0 is said to be pretabular in the lattice (N)ExtL0 , if
L is not tabular but every proper extension of L in (N)ExtL0 is tabular. In
other words, a pretabular logic in (N)ExtL0 is a maximal non-tabular logic
in (N)ExtL0 .
THEOREM 1.90 In the lattices ExtK and NExtK every non-tabular logic
is contained in a pretabular one.

68

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

1

6



6



6

.
..

G!

. 2
..
mP
H
i
P
Y
HP

I HP
@
6
P

P
n . @ H 
3   

..  ;


1  ;;

6

;
G!mn

a0 
6
a1 @
YH
H
I
6
HH
a2  b@
1  b2    
 ;

6
a3  ;;
6
a4 ;
G!22

Figure 9.

Proof By Theorem 1.85, a logic is non-tabular i it does not contain the

formula tabn , for any n < !. It follows that the union of an ascending
chain of non-tabular logics is a non-tabular logic as well. The standard use
of Zorn's Lemma completes the proof.
2
If there is a simple description of all pretabular logics in a lattice, we
obtain an e ective (modulo the description) tabularity criterion for the lattice. Indeed, take for deniteness the lattice NExtK4. How to determine,
given a formula ', whether K4  ' is tabular? We may launch two parallel
processes: one of them generates all derivations in K4  ' and stops after
nding a derivation of tabn , for some n < ! another process checks if '
belongs to a pretabular logic in NExtK4 and stops if this is the case. The
termination of the rst process means that K4  ' is tabular, while that of
the second one shows that it is not tabular.
Unfortunately, it is impossible to describe in an e ective way all pretabular logics in (N)ExtK and even (N)ExtK4: Blok 1980c] and Chagrov
1989] constructed a continuum of them. However, for smaller lattices like
NExtS4 or NExtGL such descriptions were found by Maksimova 1975b],
Esakia and Meskhi 1977] and Blok 1980c]. The ve pretabular logics in
NExtS4 were presented in Section 17 of Basic Modal Logic. In NExtGL
the picture is much more complicated.
THEOREM 1.91 (Blok 1980c, Chagrov 1989) The set of pretabular logics
in NExtGL is denumerable. It consists of the logics GL:3 = LogG! and
LogG!mn, for m 0, n 1, where G! and G!mn are the frames depicted in
Fig. 9. If hm ni 6= hk li then LogG!mn 6= LogG!kl .

Using this semantic description of pretabular logics in NExtGL, it is not

ADVANCED MODAL LOGIC

69

hard to nd nite sets of formulas axiomatizing them. Moreover, all of them
turn out to be decidable. For we have
THEOREM 1.92 Every non-tabular logic L 2 NExtK4 has a non-tabular
extension with FMP, and so every pretabular logic in NExtK4 has FMP.
Proof Since L is non-tabular and characterized by the class of its rooted
nitely generated rened frames, we have either a sequence Fi , i = 1 2 : : :,
of rooted nite frames for L of depth i, or a sequence Fi of rooted nite
frames for L of width i. In both cases the logic LogfFi : i < !g  L is
non-tabular and has FMP.
2
So we obtain the following result on the decidability of tabularity.
THEOREM 1.93 The property of tabularity is decidable in NExtS4, ExtS4,
NExtGL, ExtGL.
Since a logic in ExtK4 is locally tabular i it is determined by a frame
of nite depth, the property of local tabularity is decidable in the lattices
mentioned in Theorem 1.93 as well. However, this is not the case for ExtK4
itself.

1.14 Interpolation

One of the fundamental properties of logics is their capability to provide
explicit denitions of implicitly denable terms, which is known as the Beth
property (Beth 1953] proved it for classical logic). In the modal case we
say a logic L has the Beth property if, for any formula '(p1  : : :  pn  pn+1 )
and variables p and q di erent from p1  : : :  pn ,
'(p1  : : :  pn  p) ^ '(p1  : : : pn  q) ! (p $ q) 2 L
only if there is a formula (p1  : : : pn ) such that
'(p1  : : :  pn  p) ! (p $ (p1  : : : pn )) 2 L:
The Beth property turns out to be closely related to the interpolation property which was introduced by Craig 1957] for classical logic. Namely, we
say that a logic L has the interpolation property if, for every implication
 !  2 L, there exists a formula  , called an interpolant for  !  in L,
such that  !  2 L,  !  2 L and every variable in  , if any, occurs in
both  and  . While in abstract model theory interpolation is weaker than
Beth denability, for modal logics we have
THEOREM 1.94 (Maksimova 1992) A normal modal logic has interpolation i it has the Beth property.

70

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Say also that a normal modal logic L has the interpolation property for
the consequence relation `L , ` -interpolation for short, if every time when
 `L  , there is a formula  such that  `L  ,  `L  and Var
Var \ Var. (Here Var' is the set of all variables in '.) It should be
clear that interpolation implies ` -interpolation.
By the end of the 1970s interpolation had been established for a good
many standard modal systems. The semantical proofs, sometimes rather
sophisticated, resemble the Henkin construction of the canonical models.
Here are two examples of such proofs (which are due to Maksimova 1982b]
and Smorynski 1978]).
THEOREM 1.95 (Gabbay 1972) The logics K, K4, T, S4 have the interpolation property.

Proof We consider only S4 for the other logics the proofs are similar.
Suppose  !  62 S4 and  !  62 S4 for any  whose variables occur in
both  and  , and show that in this case  !  62 S4.
Let t = (; ) be a pair of sets of formulas such that Var' Var if
' 2 ; and Var' Var if ' 2 . Say that t is inseparable if there are
no
'i 2 ;, j 2W and  with Var Var \ Var such that
Vni=1formulas
'i !  2 S4,  ! mi=1 i 2 S4. The pair t is called complete if for
every ' and  with Var' Var and Var Var , one of the formulas
' and :' is in ; and one of  and : is in .

LEMMA 1.96 Every inseparable pair t0 = (;0 
complete inseparable pair.

0

) can be extended to a

Proof Let '1 '2  : : : and 1  2 : : : be enumerations of all formulas whose

variables occur in  and  , respectively. Dene pairs t0n = (;0n  0n ) and
tn+1 = (;n+1  n+1 ) inductively by taking

t0n =

(;n  f'n g n ) if this pair is inseparable
(;n  f:'n g n ) otherwise,

(;0n  0n  fn g) if this pair is inseparable
(;0n  0n  f:n g) otherwise
and put t = (;  ), where ; = n<! ;n ,
= n<! n . Clearly
t is complete. Suppose it is separable, i.e., for some '1  : : :  'n 2 ; ,
1  : : :  m 2 and somen  containing only those variables
that occur in
both  and  , we have i=1 'i !  2 S4 and  ! m

i
i=1 2 S4. Then
there is k < ! such that '1  : : :  'n 2 ;k and 1  : : :  m 2 k , which means
that tk is separable. So it remains to show that if t = (; ) is inseparable,
Var' Var and Var Var then

tn+1 =

S

V

S

W

ADVANCED MODAL LOGIC

71

 one of the pairs (;  f'g ) or (;  f:'g ) is inseparable and
 one of the pairs (;  fg) or (;  f:g) is inseparable.
We prove only the former claim. Suppose, on the contrary, that both pairs
are separable, i.e., there are formulas 1 , 2 in variables occurring in both
 and  such that, for some '1  : : :  'n 2 ;, 1  : : :  m 2 , we have

'1 ^ : : : ^ 'n ^ ' ! 1 2 S4 1 ! 1 _ : : : _ m 2 S4
'1 ^ : : : ^ 'n ^ :' ! 2 2 S4 2 ! 1 _ : : : _ m 2 S4:
Then we obtain ('1 ^ : : : ^ 'n ^ ') _ ('1 ^ : : : ^ 'n ^ :') ! 1 _ 2 2 S4,
1 _ 2 ! 1 _ : : : _ m 2 S4, from which
'1 ^ : : : ^ 'n ! 1 _ 2 2 S4 1 _ 2 ! 1 _ : : : _ m 2 S4
contrary to t being inseparable.
2
Now we dene a frame F = hW Ri by taking W to be the set of all
complete and inseparable pairs and, for t1 = (;1  1 ), t2 = (;2  2 ) in W ,
t1 Rt2 i 2' 2 ;1 implies ' 2 ;2 . Using the axioms 2p ! p and 2p ! 22p
of S4, one can readily check that R is a quasi-order on W , i.e., F j= S4.
Dene a valuation V in F by taking for every variable p 2 Var( !  ),
V(p) = f(; ) 2 W : either p 2 ; or p 2 Var and p 62 g. Put
M = hF Vi. By induction on the construction of formulas ' and  with
Var' Var, Var Var one can show that for every t = (; ) in F
(M t) j= ' i ' 2 ; (M t) 6j=  i  2 :
Indeed, the basis of induction follows from the denition of V and the
completeness and inseparability of t. The cases of the Boolean connectives
present no diculty. So suppose ' = 2'1 . If t j= 2'1 then, for every
t0 = (;0  0 ) 2 t", we have t0 j= '1 and so '1 2 ;0 . Suppose 2'1 62 ;. Then
:2'1 2 ;. Consider the pair t0 = (;0  0 ), where
;0 = f:'1 g  f : 2 2 ;g 0 = f: : :2 2 g
and show that it is inseparable. Assume otherwise. Then there is  with
Var Var \ Var such that, for some formulas 21 : : :  2n 2 ;,
:2n+1  : : :  :2m 2 ,
:'1 ^ 1 ^ : : : ^ n !  2 S4  ! :n+1 _ : : : _ :m 2 S4:
It follows that
:2'1 ^ 21 ^ : : : ^ 2n ! 3 2 S4

72

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

3 ! :2n+1 _ : : : _ :2m 2 S4
contrary to t being inseparable. Let t0 = (;0  0 ) be a complete inseparable
extension of t0 . By the denition of t0 , we have tRt0 and so '1 2 ;0 , contrary
to :'1 2 ;0 ;0 and t0 being inseparable.
Suppose now that 2'1 2 ;. Then for every t0 = (;0  0 ) such that tRt0,
we have '1 2 ; and so t0 j= '1 . Consequently, t j= 2'1 . The formula  is
treated in the dual way.
To complete the proof it remains to observe that M 6j=  !  .
2
This proof does not always go through for di erent kinds of logics. However, sometimes suitable modications are possible.
THEOREM 1.97 GL has the interpolation property.
Proof Suppose  !  has no interpolant in GL. Our goal is to construct
a nite irreexive transitive frame refuting  !  .
This time we consider nite pairs t = (; ) such that all formulas in ;
and are constructed from variables and their negations using ^, _, 2, 3.
Without loss of generality we will assume  and  to be formulas of that
sort. Say that t is separable if there is a formula  with Var Var\Var
such that ; !  2 GL and  !
2 GL. It should be clear that if
t = (; ) is a nite inseparable pair then in the same way as in the proof
of Theorem 1.95 but taking only subformulas of  and  we can obtain
a nite inseparable pair t? = (;?  ? ) satisfying the conditions: for every
' 2 Sub and  2 Sub , one of the formulas ' and :' (an equivalent
formula of the form under consideration, to be more precise) is in ;? and
one of  and : is in ? .
Now we construct by induction a nite rooted model for GL refuting
 !  . As its root we take (fg?  f g? ). If we have already put in our
model a pair t = (; ) and it has not been considered yet, then for every
3' 2 ; and every 2 2 , we add to the model the pairs
t1 = (f 2 2:' ' : 2 2 ;g?  f 3 : 3 2 g? )
t2 = f 2 : 2 2 ;g? f 3 3:  : 3 2 g?):
One can readily show that if t is inseparable then t1 and t2 are also inseparable. Put tR0 t1 and tR0 t2 . The process of adding new pairs must
eventually terminate, since each step reduces the number of formulas of the
form 3' and 2 in the left and right parts of pairs. Let W be the set of
all pairs constructed in this way and R the transitive closure of R0 . Clearly,
the resulting frame F = hW Ri validates GL. Dene a valuation V in F by
taking, for each variable p,
V(p) = f(; ) 2 W : p 2 ;g:

V

W

ADVANCED MODAL LOGIC

73

As in the proof of Theorem 1.95, it is easily shown that  !  is refuted in
F under V.
2
To clarify the algebraic meaning of interpolation we require the following
well known proposition.
PROPOSITION 1.98 If r is a normal lter12 in a modal algebra A then
the relation r , dened by a r b i a $ b 2 r, is a congruence relation.
The map r 7! r is an isomorphism from the lattice of normal lters in A
onto the lattice of congruences in A.
Denote by A=r the quotient algebra A= r and let kakr = fb : a r bg.
Say that a class C of algebras is amalgamable if for all algebras A0 , A1,
A2 in C such that A0 is embedded in A1 and A2 by isomorphisms f1 and f2,
respectively, there exist A 2 C and isomorphisms g1 and g2 of A1 and A2
into A with g1 (f1 (x)) = g2 (f2 (x)), for any x in A0. If in addition we have
gi (x)  gj (y) implies 9z 2 A0 (x i fi (z ) and fj (z ) j y)
for all x 2 Ai , y 2 Aj such that fi j g = f1 2g, then C is called superamalgamable. Here Ai is the universe of Ai and i its lattice order.
THEOREM 1.99 (Maksimova 1979) L has the interpolation property i the
variety AlgL of modal algebras for L is superamalgamable. L has the ` interpolation property i AlgL is amalgamable.
Proof We prove only the former claim. ()) Suppose L has the interpolation property and A0 , A1, A2 are modal algebras for L such that A0 is
a subalgebra of both A1 and A2 . With each element a 2 Ai , i = 0 1 2,
we associate a variable pia in such a way that, for a 2 A0 , p0a = p1a = p2a.
Denote by Li the language with the variables pia , for a 2 Ai , i = 0 1 2, and
let L = L1  L2 . We will assume that L is the language of L.
Fix the valuation Vi of Li in Ai , dened by Vi (pia ) = a, and put
#i = f' 2 ForLi : Vi (') = >g:
Let # be the closure of #1  #2  L under modus ponens. We show that,
for every ' 2 ForLi ,  2 ForLj such that fi j g = f1 2g,
' !  2 # i 9 2 ForL0 (' !  2 #i and  !  2 #j ): (13)
Suppose ' !  2 #. Then there exist nite sets ;i #i and ;j #j such
that
;i ^ ' ! ( ;j ! ) 2 L:

^

^

12 A lter r is normal (or open, as in Section 10 of Basic Modal Logic) if 2a 2 r
whenever a 2 r.

74

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Since L has interpolation, there is a formula  2 ForL0 such that

^ ;i ^ ' !  2 L ^ ;j ! ( ! ) 2 L

from which ' !  2 #i and  !  2 #j . The converse implication is
obvious.
Now construct an algebra A by taking the set fk'k : ' 2 #g as its
universe, where k'k = f : ' $  2 #g, k'k ^ kk = k' ^ k and
$k'k = k $ 'k, for $ 2 f: 2g. One can readily prove that A 2 AlgL.
Dene maps gi from Ai into A by taking gi (a) = kpiak. It is not dicult to
show that gi is an embedding of Ai in A. And for a 2 A0 , we have

g1 (a) = kp0a k = g2 (a):
It remains to check the condition for superamalgamability: Suppose a 2 Ai ,
b 2 Aj , fi j g = f1 2g, and gi (a)  gj (b). Then gi (a) ! gj (b) = > and
so kpia ! pjb k = >, i.e., pia ! pjb 2 #. By (13), we have  2 ForL0 with
V() = c such that a i c j b.
(() Assuming AlgL to be superamalgamable, we show that L has the
interpolation property. To this end we require
LEMMA 1.100 Suppose A0 is a subalgebra of modal algebras A1 and A2 ,
a 2 A1 , b 2 A2 and there is no c 2 A0 such that a 1 c 2 b. Then
there are ultralters r1 in A1 and r2 in A2 such that a 2 r1 , b 62 r2 and
r1 \ A0 = r2 \ A0 .
Suppose '(p1  : : :  pm  q1  : : :  qn ) and (q1  : : :  qn  r1  : : :  rl ) are formulas for which there is no (q1  : : :  qn ) such that ' !  2 L and  !  2 L.
We show that in this case there exists an algebra A 2 VarL refuting ' ! .
Let A00 , A01 and A02 be the free algebras in AlgL generated by the sets
fc1  : : :  cn g, fa1  : : :  am  c1  : : :  cn g and fc1  : : :  cn  b1  : : :  bl g, respectively.
According to this denition, A00 is a subalgebra of both A01 and A02 . By
Lemma 1.100, there are ultralters r1 in A01 and r2 in A02 such that we
have '(a1  : : :  am c1  : : :  cn ) 2 r1 and (c1  : : :  cn  b1  : : :  bl ) 62 r2 . Dene normal lters
ri = fa 2 A0i : 8m < ! 2m a 2 ri g

and put A1 = A01 =r1 , A2 = A02 =r2 . Construct an algebra A0 by taking
A0 = fkakr1 : a 2 A00 g. By the denition, A0 is a subalgebra of A1 , i.e., is
embedded in A1 by the map f1 (x) = x. One can show that A0 is embedded
in A2 by the map f2 (kxkr1 ) = kxkr2 . Then there are an algebra A for L
and isomorphisms g1 and g2 of A1 and A2 into A satisfying the conditions
of superamalgamability. Dene a valuation V in A by taking V(pi ) =




ADVANCED MODAL LOGIC

75


H
Y

H 
H
H
;  H H H
;
H
I 
@
;
Y
H
;

H
@ 
 H H H ; ; @
I  
@

@

@



@
@ 

;

;

H
Y

H



Figure 10.

g1 (kai kr1 ), V(qj ) = g1 (kcj kr1 ) = g2 (kcj kr2 ) and V(rk ) = g2(kbk kr2 ).
Then V(') 6 V() because otherwise there would exist fi j g = f1 2g and
z 2 A0 such that V(') i fi (z ) and fj (z ) j V(). Thus, A 6j= ' !  and
so ' !  62 L.
2
Using this theorem Maksimova 1979] discovered a surprising fact: there
are only nitely many logics in NExtS4 with the interpolation property
(not more than 38, to be more exact) and all of them turned out to be
union-splittings. By Theorem 1.12, we obtain then
THEOREM 1.101 (Maksimova 1979) There is an algorithm which, given a
modal formula ', decides whether S4  ' has interpolation.
We illustrate this result by considering a much simpler class of logics.
THEOREM 1.102 Only four logics in NExtS5 have the interpolation property: S5 itself, the logic of the two-point cluster, Triv and For.

Proof We have already demonstrated how to prove that a logic has interpolation. So now we show only that no logic L in NExtS5 di erent from

those mentioned in the formulation has the interpolation property. Suppose
on the contrary that L has interpolation. We use the amalgamability of the
variety of modal algebras for L to show that an arbitrary big nite cluster
is a frame for L, from which it will follow that L = S5.

76

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Figure 10 demonstrates two ways of reducing the three-point cluster to
the two-point one. By the amalgamation property, there must exist a cluster reducible to the two depicted copies of the two-point cluster, with the
reductions satisfying the amalgamation condition. It should be clear from
Fig. 10 that such a cluster contains at least four points. By the same scheme
one can prove now that every n-point cluster validates L.
2
It would be naive to expect that such a simple picture can be extended
to classes like NExtK4 or NExtK. Even in NExtGL the situation is quite
di erent from that in NExtS4: Maksimova 1989] discovered that there is
a continuum of logics in NExtGL having the interpolation property. This
result is based upon the following observation. For L 2 NExtK4, we call a
formula (p) conservative in NExtL if

2+ ((?) ^ (p) ^ (q)) ! (p ! q) ^ (2p) 2 L:
For example, in NExtS4 conservative are 23p ! 32p, 23p $ 32p, and
2p $ 3p.
THEOREM 1.103 (Maksimova 1987) If L 2 NExtK4 has the interpolation
property and formulas i , for i 2 I , are conservative in NExtL, then the
logic L  fi : i 2 I g also has the interpolation property.
Proof Suppose ' !  2 L fi : i 2 I g. Then there is a nite J I , say
J = f1 : : : lg, such that ' !  2 L  fi : i 2 J g and so, as follows from

the denition of conservative formulas and the Deduction Theorem for K4,

2+

^l (j (?) ^ j (p ) ^ : : : ^ j (pn)) ! (' ! ) 2 L
1

j =1

where p1  : : :  pm  pm+1  : : :  pk and pm+1 : : :  pk  pk+1  : : :  pn are all the
variables in ' and , respectively. Consequently

2+

^l (j (?) ^ j (p ) ^ : : : ^ j (pk )) ^ ' !
1

j =1

(2+

^l (j (pm ) ^ : : : ^ j (pn)) ! ) 2 L:

j =1

+1

Since L has the interpolation property, there is (pm+1  : : :  pk ) such that
l
^
2 (j (?) ^ j (p ) ^ : : : ^ j (pk )) ^ ' !  2 L
+

j =1

1

ADVANCED MODAL LOGIC

2+

77

^l (j (pm ) ^ : : : ^ j (pn)) ! ( ! ) 2 L:

j =1

+1

Then we obtain ' !  2 L  fi : i 2 I g and  !  2 L  fi : i 2 I g,
i.e.,  is an interpolant for ' !  in L  fi : i 2 I g.
2
Using the formulas

i = 2+ (3i+1 > ^ 2i+2 ? ! 2i+1 p _ 2i+1 :p)

which are conservative in NExtGL, one can readily construct a continuum
of logics in this class with the interpolation property. The set of logics in
NExtGL without interpolation is also continual.
In general, an interpolant  for an implication  !  2 L depends on
both  and  . Say that a logic L has uniform interpolation if, for any
nite set of variables $ and any formula , there exists a formula  such
that Var $ and  !  2 L,  !  2 L whenever Var \ Var $
and  !  2 L. In this case  is called a post-interpolant for  and
$. Roughly speaking, a logic has uniform interpolation if we can choose
an interpolant for  !  2 L independly from the actual shape of  .
Uniform interpolation was rst investigated by Pitts 1992] who proved that
intuitionistic logic enjoys it. It is fairly easy to nd multiple examples
of modal logics with uniform interpolation by observing that any locally
tabular logic with interpolation has uniform interpolation as well. Indeed,
for every formula  and every set of variables $, we can dene a postinterpolant  as the conjunction of a maximal set of pairwise non-equivalent
in L formulas  0 such that Var 0 $ and  !  0 2 L (which is nite in view
of the local tabularity of L). It follows, for instance, that S5 has uniform
interpolation. In general, however, interpolation does not imply uniform
interpolation: Ghilardi and Zawadowski 1995] showed that S4 does not
enjoy the latter, witness the following formula without a post-interpolant
for frg in S4

p ^ 2(p ! 3q) ^ 2(q ! 3p) ^ 2(p ! r) ^ 2(q ! :r):
Only a few positive results on the uniform interpolation of modal logics
are known: Shavrukov 1993] proved it for GL, Ghilardi 1995] for K, and
Visser 1996] for Grz.
A property closely related to interpolation is so called Hallden completeness. A logic L is said to be Hallden complete if ' _  2 L and
Var' \ Var =  imply ' 2 L or  2 L. Since every variable free formula is equivalent in D either to > or to ?, L 2 ExtD is Hallden complete
whenever it has interpolation. K, K4, GL are examples of Hallden incomplete logics with interpolation: each of them contains 3> _ :3> but not

78

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

3> and :3>. On the other hand, S4:3 is a Hallden complete logic (see

van Benthem and Humberstone 1983]) without interpolation (see Maksimova 1982a]). Actually, there is a continuum of Hallden complete logics in
NExtS4 (see Chagrov and Zakharyaschev 1993]).
Hallden completeness has an interesting lattice-theoretic characterization.
THEOREM 1.104 (Lemmon 1966c) A logic L 2 ExtK is Hallden complete
i it is -irreducible in ExtL.
Since the lattice ExtS5 is linearly ordered by inclusion, all logics above
S5 are Hallden complete. There are various semantic criteria for Hallden
completeness (see e.g. Maksimova 1995]). Here we note only the following
generalization of the result of van Benthem and Humberstone 1983].

T

THEOREM 1.105 Suppose a logic L 2 ExtK is characterized by a class
C of descriptive rooted frames with distinguished roots. Then L is Hallden
complete i, for all frames hF1  d1 i and hF2  d2 i in C , there is a frame hF di
for L reducible13 to both hF1  d1 i and hF2  d2 i.
For more results and references on Hallden completeness consult Chagrov
and Zakharyaschev 1991].
2 POLYMODAL LOGICS
So far we have conned ourselves to considering modal logics with only one
necessity operator. From a theoretical point of view this restriction is not
such a great loss as it may seem at rst sight. In fact, really important
concepts of modal logic do not depend on the number of boxes and can
be introduced and investigated on the basis of just one. We shall give a
precise meaning to this claim in Section 2.3 below where it is shown that
polymodal logic is reduced in a natural way to unimodal logic. However,
there are at least two reasons for a detailed discussion of polymodal logic
in this chapter.
First, a number of interesting phenomena are easily missed in unimodal
logic and actually appear in a representative form only in the polymodal
case. For example, with the exception of NExtK4.3 and QCSF all known
general decidability results in unimodal logic have been obtained by proving
the nite model property. In fact, nearly all natural classes of logics in
NExtK turned out to be describable by their nite frames. The situation
drastically changes with the addition of just one more box. Even in the
case of linear tense logics or bimodal provability logics one has to start with
13

By reductions that map d to di .

ADVANCED MODAL LOGIC

79

a thorough investigation of their innite frames: FMP becomes a rather
rare guest. While the result on NExtK4.3 indicated the need for general
methods of establishing decidability without FMP, this need becomes of
vital importance only in the context of polymodal logic.
The second reason is that various applications of modal logic require
polymodal languages. For example, in tense logic we have two necessitylike operators 21 and 22 . One of them, say the former, is interpreted as \it
will always be true" and the other as \it was always true". Kripke frames for
tense logics are structures hW R1  R2 i with two binary relations R1 and R2
such that R2 coincides with the converse R1;1 of R1 (which reects the fact
that a moment x is earlier than y i y is later than x). The characteristic
axioms connecting the two tense operators are
p ! 21 32p and p ! 22 31p:
For more information about tense systems consult Basic Tense Logic.
Another example is basic temporal logic in which we have two necessitylike operators: one of them|usually called Next|is interpreted by the
successor relation in ! and the other by its transitive and reexive closure. Details can be found in Segerberg 1989]. Propositional dynamic logic
PDL and its extensions, like deterministic PDL, can also be regarded as
polymodal logics (see Dynamic Logic).
A number of provability logics use two or more modal operators see e.g.
Boolos 1993]. In GLB, for instance, we have one operator 21 understood
as provability in PA and another operator 22 interpreted as !-provability
in PA. The unimodal fragments of GLB coincide with GL. The axioms
connecting 21 and 22 are
21 p ! 22 p and 31p ! 22 31p:
In epistemic logics we need an operator 2i for each agent i 2i ' is interpreted as \agent i believes (or knows) '". One possible way to axiomatize
the logic of knowledge with m agents is to take the axioms of S5 for each
agent without any principles connecting di erent 2i and 2j . We denote
m
the resultant logic by m
i=1 S5. Often i=1 S5 is extended by the common
knowledge operator C with the intended meaning
C' = E' ^ E2 ' ^ : : : ^ En' ^ : : :  where E' = m
i=1 2i '
(see e.g. Halpern and Moses 1992] and Meyer and van der Hoek 1995]).
The reader will nd more items for this list in other chapters of the
Handbook.
From the semantical point of view, many standard polymodal logics
can be obtained by applying Boolean or various natural closure operators to the accessibility relations of Kripke frames. For instance, in frames

N

N

V

80

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

hW R1  : : :  Rn i for epistemic logic the common knowledge operator is interpreted by the transitive closure of R1  : : :  Rn . Tense frames result
from usual hW Ri by adding the converse of R. Humberstone 1983] and
Goranko 1990a] study the bimodal logic of inaccessible worlds determined
by frames of the form W R W 2 ; R . This list of examples can be continued for a general approach and related topics consult Goranko 1990b],
Gargov et al. 1987], Gargov and Passy 1990].
Let us see now how polymodal logics in general t into the theory developed so far. We begin by demonstrating how the concepts introduced in
the unimodal case transfer to polymodal logic and showing that a few general results|like Sahlqvist's and Blok's Theorems|have natural analogues
in polymodal logic. We hope to convince the reader that up to this point
no new diculties arise when one switches from the unimodal language to
the polymodal one. After that, in Section 2.2, we start considering subtler
features of polymodal logics.





2.1 From unimodal to polymodal

Let LI be the propositional language with a nite number of necessity operators 2i , i 2 I . A normal polymodal logic in LI is a set of LI -formulas
containing all classical tautologies, the axioms 2i (p ! q) ! (2i p ! 2i q)
for all i 2 I , and closed under substitution, modus ponens and the rule of
necessitation '=2i ' for every i 2 I . If the language is clear from the context, we call these logics just (normal) modal logics and denote by NExtL
the family of all normal extensions of L (in the language LI ). The smallest
normal modal logic with n necessity operators is denoted by Kn (K = K1 ,
of course).
Given a logic L0 in LI and a set of LI -formulas ;, we again denote by
L0  ; the smallest normal logic (in LI ) containing L0  ;. A number
of other notions and results also transfer in a rather straightforward way,
e.g. Theorems 1.4 and 1.6, Proposition 1.5 and all concepts involved in their
formulations. More care has to be taken to generalize Theorems 1.1, 1.2 and
1.3. Denote by M I the set of non-empty strings (words) over f2i : i 2 I g
which do not contain any 2i twice and put

^

^

2I ' = fM ' : M 2 M I g 2I m ' = f2nI ' : n  mg:
In the language LI the operator 2I serves as a sort of surrogate for 2 in

K. For example, the following polymodal version of Theorem 1.1 holds.

THEOREM 2.1 (Deduction) For every modal logic L in LI , every set of
LI -formulas ;, and all LI -formulas ' and ,
;  `L ' i 9m 0 ; `L 2I m  ! ':

ADVANCED MODAL LOGIC

81

Theorems 1.2 and 1.3 can be reformulated analogously by replacing 2
with 2I (a logic L in LI is n-transitive if it contains 2I n p ! 2nI +1 p).
Basic semantic concepts are lifted to the polymodal case in a straightforward manner. The algebraic counterpart of L 2 NExtKn is the variety of Boolean algebras with n unary operators validating L. A structure
F = hW hRi : i 2 I i P i is called a (general polymodal) frame whenever
every hW Ri  P i, for i 2 I , is a unimodal frame. We then put

2i X = fx 2 W : 8y (xRi y ! y 2 X )g:
Dierentiated, rened and descriptive frames and the truth-preserving operations can also be dened in the same component-wise way. For instance,
a frame F = hW hRi : i 2 I i P i is di erentiated if all the unimodal frames
hW Ri  P i, for i 2 I , are di erentiated. F = hW hRi : i 2 I i P i is a (generated) subframe of G = hV hSi : i 2 I i Qi if all hW Ri  P i are (generated)
subframes of hV Si  Qi, and f is a reduction of F to G if f is a reduction of
hW Ri  P i to hV Si  Qi, for every i 2 I .
There are some exceptions to this rule. A point r is called a root of F if it
is a root of the unimodal frame hW i2I Ri i. This does not mean that r is a
root of all unimodal reducts of F. Another important exception: as before,
a polymodal frame is {-generated if the algebra F+ is {-generated however,
this does not mean that the unimodal reducts of F are {-generated.

S

Splittings and the degree of Kripke incompleteness The semantic

criterion of splittings by nite frames given in Theorem 1.15 transfers to
polymodal logics by replacing 2 with 2I . Again, all nite rooted frames
split NExtL0 , if L0 is an n-transitive logic in LI . Notice, however, that
n-transitivity is a rather strong condition in the polymodal case. For example, it is easily checked that the fusion S5 & S5 as well as the minimal
tense logic K4:t containing K4 are not n-transitive, for any n < ! (see
Sections 2.2 and 2.4 for precise denitions). In fact, only  splits the lattice
NExt(S5 & S5) and only  splits NExtK4:t (see Wolter 1993] and Kracht
1992], respectively).
Call a frame hW hRi : i 2 I ii cycle free if the unimodal frame hW i2I Ri i
is cycle free. Kracht 1990] showed that precisely the nite cycle free frames
split NExtKn .
It is not dicult now to extend Blok's result on the degree of Kripke
incompleteness to the polymodal case. Note, however, that the degree of
incompleteness of For in NExtKn is 2@0 whenever n 2. So, we do not have
a polymodal analog of Makinson's Theorem. (An example of an incomplete
maximal consistent logic in NExtK2 is the logic determined by the tense
frame C(0 ) introduced in Section 2.5).

S

82

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 2.2 Let n > 1. If L is a union-splitting of NExtKn , then L is
strictly Kripke complete. Otherwise L has degree of Kripke incompleteness
2@0 in NExtKn .

Sahlqvist's Theorem and persistence The proof of the following poly-

modal version of Sahlqvist's Theorem is a straightforward extension of the
proof in the unimodal case. Say that ' is a Sahlqvist formula (in LI ) if the
result of replacing all 2i and 3i , i 2 I , in ' with 2 and 3, respectively, is
a unimodal Sahlqvist formula.
THEOREM 2.3 Suppose that ' is equivalent in NExtKn to a Sahlqvist formula. Then Kn  ' is D-persistent, and one can eectively construct a rst
order formula (x) in R1  : : :  Rn and = such that, for every descriptive or
Kripke frame F and every point a in F, (F a) j= ' i F j= (x)a].

N

Bellissima's result on the DF -persistence of all logics in NExtAltn has
a polymodal analog as well. Denote by i2I Altn the smallest polymodal
logic in LI containing Altn in all its unimodal fragments. It is easy to see
that every L 2 NExt i2I Altn is DF -persistent and so Kripke complete.
However, in contrast to the lattice NExtAlt1 |which is countable and all
logics in which have FMP (see Segerberg 1986] and Bellissima 1988])|
the lattice NExt(Alt1 & Alt1 ) is rather complex: as was shown by Grefe
1994], it contains logics without FMP (even without nite frames at all)
and uncountably many maximal consistent logics.

N

Some FMP results Fine's Theorem on uniform logics can be extended

to a suitable class of polymodal logics in LI , namely those logics that contain 3i>, for all i 2 I , and are axiomatizable by formulas ' in which all
maximal sequences of nested modal operators coincide with respect to the
distribution of the indices i of 2i and 3i , i 2 I .
Now consider a result of Lewis 1974] which we have not proved in its
unimodal formulation. Call a normal polymodal logic non-iterative if it is
axiomatizable by formulas without nested modalities. Examples of noniterative logics are T = K  2p ! p, Altm & Altn and K2  22 p ! 21 p.
THEOREM 2.4 (Lewis 1974) All non-iterative normal logics have FMP.

Proof Suppose the axioms of L = Kn  ; have no nested modal operators and ' 62 L. By a '-description we mean any set of subformulas of
' together with the negations of the remaining formulas in Sub'. For

each L-consistent '-description % select a maximal L-consistent set 
containing %. Denote by W the (nite) set of the selected  and dene

ADVANCED MODAL LOGIC

83

F = hW hRi : i 2 I ii and M = hF Vi by taking


Ri  i 3 i

^& 2



and V(p) = f  2 W : p 2  g. It is easily proved that (M  ) j=  i
 2  , for all subformulas  of ' and  2 W . Hence F 6j= '. It is also
easy to see that for all truth-functional compounds  of subformulas in ',
(M



) j= 3i  i 3i 2



:

(14)

Consider now a model M0 = hF V0 i and  2 ;. For each variable p put

p =

_ n^ % :



o

2 V(p)

and denote by 0 the result of substituting p for p, for each p in . Then
M0 j=  i M j= 0 . In view of (14), we have M j= 0 because 0 has no
2
nested modalities. Therefore, F j=  and so F j= L.

Tabular Logics Needless to say that all polymodal tabular logics are

nitely axiomatizable and have only nitely many extensions. (The proof is
the same as in the unimodal case.) A more interesting observation concerns
the complexity of polymodal logics whose unimodal fragments are tabular
or pretabular. In fact, it is not dicult to construct two tabular unimodal
logics L1 and L2 such that their fusion L1 & L2 has uncountably many
normal extensions (see e.g. Grefe 1994]). However, those logics are DF persistent and so Kripke complete. Wolter 1994b] showed that the lattice

NExtT can be embedded into the lattice NExt(Log 6& S5) in such a way
that properties like FMP, decidability and Kripke completeness are reected
under this embedding. It follows that almost all \negative" phenomena of
modal logic are exhibited by bimodal logics one unimodal fragment of which
is tabular and the other pretabular.

2.2 Fusions

The simplest way of constructing polymodal logics from unimodal ones is
to form the fusions (alias independent joins) of them. Namely, given two
unimodal logics L1 and L2 in languages with the same set of variables and
distinct modal operators 21 and 22 , respectively, the fusion L1 & L2 of
L1 and L2 is the smallest bimodal logic to contain L1  L2. If ;1 and
;2 axiomatize L1 and L2, then L1 & L2 is axiomatized by ;1  ;2 , i.e.,
L1 & L2 = K2  ;1  ;2 . So the fusions are precisely those bimodal logics
that are axiomatizable by sets of formulas each of which contains only one

84

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

of 21 , 22 . From the model-theoretic point of view this means that a frame
hW R1  R2  P i validates L1 & L2 i hW Ri  P i j= Li for i = 1 2.
PROPOSITION 2.5 (Thomason 1980) If logics L1 and L2 are consistent,
then L1 & L2 is a conservative extension of both L1 and L2 .

Proof Suppose for deniteness that ' 62 L1, for some formula ' in the
language of L1 , and consider the Tarski{Lindenbaum algebras









AL1 (!) = A ^A  :A  21 and AL2 (!) = B ^B  :B  22 :
The Boolean reducts of them are countably innite atomless Boolean algebras which are known to be isomorphic (see e.g. Koppelberg 1988]). So
we
assume that
A = B , ^A = ^B , :A = :B . Since AL1 (!) refutes ',
Amay

A
A
2
^  :  21  22 is then an algebra for L1 & L2 refuting '.
Having constructed the fusion of logics, it is natural to ask which of
their properties it inherits. For example, the rst order theory of a single
equivalence relation has the nite model property and is decidable, but the
theory of two equivalence relations is undecidable and so does not have the
nite model property (see Janiczak 1953]). So neither decidability nor the
nite model property is preserved under joins of rst order theories. On
the other hand, as was shown by Pigozzi 1974], decidability is preserved
under fusions of equational theories in languages with mutually disjoint sets
of operation symbols.
For modal logics we have:
THEOREM 2.6 Suppose L1 and L2 are normal unimodal consistent logics
and P is one of the following properties: FMP, (strong) Kripke completeness, decidability, Hallden completeness, interpolation, uniform interpolation. Then L = L1 & L2 has P i both L1 and L2 have P .

Proof We outline proofs of some claims in this theorem the reader can

consult Fine and Schurz 1996], Kracht and Wolter 1991], and Wolter
1997b] for more details.
The implication ()) presents no diculties. So let us concentrate on
((). With each formula ' of the form 2i  we associate a new variable
q' which will be called the surrogate of '. For a formula ' containing
no surrogate variables, denote by '1 the formula that results from ' by
replacing all occurrences of formulas 22 , which are not within the scope
of another 22 , with their surrogate variables q22  . So '1 is a unimodal
formula containing only 21 . Denote by %1 (') the set of variables in '
together with all subformulas of 22  2 Sub'. The formula '2 and the set
%2(') are dened symmetrically.

ADVANCED MODAL LOGIC

85

Suppose now that both L1 and L2 are Kripke complete and ' 62 L. To
prove the completeness of L we construct a Kripke frame for L refuting
'. Since we know only how to build refutation frames for the unimodal
fragments of L, the frame is constructed by steps alternating between 21
and 22 . First, since L1 is complete, there is a unimodal model M based
on a Kripke frame for L1 and refuting '1 at its root r. Our aim now is
to ensure that the formulas of the form 22  have the same truth-values as
their surrogates q22  . To do this, with each point x in M we can associate
the formula

^

^

'x = f 2 %1(') : (M x) j= 1 g ^ f: :  2 %1(') (M x) 6j= 1 g
construct a model Mx based on a frame for L2 and satisfying '2x at its
root y, and then hook Mx to M by identifying x and y. After that we can
switch to 21 and in the same manner ensure that formulas 21  have the
same truth-values as q21  at all points in every Mx . And so forth.
However, to realize this quite obvious scheme we must be sure that 'x
is really satisable in a frame for L2 , which may impose some restrictions
on the models we choose. First, one can show that in the construction
above it is enough to deal with points x accessible from r by at most m =
md(') steps. Let X be the set of all such points. Now, a sucient and
necessary condition for 'x to be L- (and so L2-) consistent can be formulated
as follows. Call a %1 (')-description the conjunction of formulas in any
maximal L-consistent subset of %1 (')  f: :  2 %1(')g. It should be
clear that 'x is L-consistent i it is a %1 (')-description. Denote by #1 (')
the set of all %1 (')-descriptions. It follows that all 'x , for x 2 X , are
L-consistent i (M r) j= 21 m ( #1 ('))1 . In other words, we should start
with a model M satisfying '1 ^ 21 m ( #1 ('))1 at its root r. Of course,
the subsequent models Mx , for x 2 X , must satisfy '2x ^ 22 m ( #2 ('x ))2 ,
where #2 ('x ) is the set of all %2('x )-descriptions, etc.
In this way we can prove that Kripke completeness is preserved under
fusions. The preservation of strong completeness and FMP can be established in a similar manner. The following lemma plays the key role in the
proof of the preservation of the four remaining properties.

W

W

W

LEMMA 2.7 The following conditions are equivalent for every ':
(i) ' 2 L1 & L2 
(ii) 21 m ( #1 ('))1 ! '1 2 L1 , where m = md(')
(iii) 22 m ( #2 ('))2 ! '2 2 L2 .

W
W

For Kripke complete L1 and L2 this lemma was rst proved by Fine and
Schurz 1996] and Kracht and Wolter 1991] actually, it is an immediate
consequence of the consideration above. The proof for the arbitrary case is

86

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

also based upon a similar construction combined with the algebraic proof
of Proposition 2.5 for details see Wolter 1997b].
Now we show how one can use this lemma to prove the preservation
of the remaining properties. Dene a1 (') to be the length of the longest
sequence 22  21  22  : : : of boxes starting with 22 such that a subformula
of the form 22 (: : : 21 (: : : 22 (: : : : : :))) occurs in '. The function a2 (') is
dened analogously by exchanging 21 and 22 , and a(') = a1 (') + a2 (').
It is easy to see that

_

_

a(') > a( #1 (')) or a(') > a( #2 (')):
The preservation of decidability, Hallden completeness, interpolation, and
uniform interpolation can be proved by induction on a(') with the help
of Lemma 2.7. We illustrate the method only for Hallden completeness.
Notice rst that, modulo the Boolean equivalence, we have

_ # (' _ ) = _ # (') ^ _ # () ^ ^ (' )
1

1

1

where
(' ) = f1 ! :2 : 1 2 #1 (') 2 2 #1 () 1 ! :2 2 Lg:
Suppose both L1 and L2 are Hallden complete. By induction on n = a('_)
we prove that ' _  2 L implies ' 2 L or  2 L whenever ' and  have no
common variables. The basis of induction is trivial. So suppose a(' _ ) =
n > 0 and ' _  2 L. We may also assume that a(' _ ) > a( #1 (' _ )):
By the induction hypothesis, it follows that (' ) = . Hence, up to the
Boolean equivalence, #1 (' _ ) = #1 (') ^ #1 () and, by Lemma 2.7,

W

W

W
W
_
_
2 m ( # ('))1 ^ 2 m ( # ())1 ! (' _ )1 2 L 

1

1

for m = md(' _ ). Then

_


1

1

1

_

(21 m ( #1 ('))1 ! '1 ) _ (21 m ( #1 ())1 ! 1 ) 2 L1
and, by the Hallden completeness of L1 , one of the disjuncts in this formula
belongs to L1 . By Lemma 2.7, this means that ' 2 L or  2 L.
2

Remark. This theorem can be generalized to fusions of polymodal logics
with polyadic modalities.
Note that in languages with nitely many variables both GL:3 and K
are strongly complete but GL:3 & K is not strongly complete even in the
language with one variable (see Kracht and Wolter 1991]).

ADVANCED MODAL LOGIC

87

It is natural now to ask whether there exist interesting axioms ' containing both 21 and 22 and such that (L1 & L2 )  ' inherits basic properties of
L1  L2 2 NExtK. Let us start with the observation that even such a simple
axiom as 21 p $ 22 p destroys almost all \good" properties because (i) we
can identify (L1 & L2 )  21 p $ 22 p with the sum of the translation of L1
and L2 into a common unimodal language and (ii) such properties as FMP,
decidability, and Kripke completeness are not preserved under sums of unimodal logics (see Example 1.64 and Chagrov and Zakharyaschev 1997]).
Even for the simpler formula 22 p ! 21 p no general results are available.
To demonstrate this we consider the following way of constructing a bimodal
logic Lu for a given L 2 NExtK:

Lu = (L & S5)  22 p ! 21 p:
The modal operator 22 in Lu is called the universal modality. Its meaning
is explained by the following lemma:
LEMMA 2.8 (Goranko and Passy 1992) For every normal unimodal logic L
and all unimodal formulas ' and ,

' `L  i `Lu 22 ' ! :

Proof Follows immediately from Theorem 1.19 (ii), since
hW R P i j= L i hW R W ' W P i j= Lu

for every frame hW R P i and every unimodal logic L.

2

The universal modality is used to express those properties of frames F =
hW R W ' W i that cannot be expressed in the unimodal language. For
example, F validates 22 (p ! 31p) ! :p i it contains no innite Rchains. Recall that there is no corresponding unimodal axiom, since K is
determined by the class of frames without innite R-chains. We refer the
reader to Goranko and Passy 1992] for more information on this matter.
THEOREM 2.9 (Goranko and Passy 1992) For any L 2 NExtK,
(i) L is globally Kripke complete i Lu is Kripke complete
(ii) L has global FMP i Lu has FMP.

Proof We prove only (i). Suppose that Lu is Kripke complete and ' 6`L .

Then by Lemma 2.8, 22 ' !  62 Lu and so 22 ' !  is refuted in a Kripke
frame F = hW R1  R2 i for Lu . We may assume that R2 = W ' W . But
then ' `L  is refuted in hW R1 i. Conversely, suppose that L is globally
Kripke complete and ' 62 Lu , for a (possibly bimodal) formula '. Using

88

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

the properties of S5 it is readily checked that ' is (e ectively) equivalent
in Ku to a formula '0 which is a conjunction of formulas  of the form
 = 0 _ 321 _ 22 2 _ 22 3 _ : : : _ 22 n
such that 0  : : :  n are unimodal formulas in the language with 21 . Let
 be a conjunct of '0 such that  62 Lu . Then :1 6`L i , for every
i 2 f0 2 3 : : : ng. Since L is globally complete, we have Kripke frames
hWi  Ri i for L refuting :1 `L i , for i 2 f0 2 : : : ng. Denote by hW Ri
the disjoint union of those frames. Then hW R W ' W i is a Kripke frame
for Lu refuting '.
2
We have seen in Section 1.5 that there are Kripke complete logics (logics
with FMP) which do not enjoy the corresponding global property. In view
of Theorem 2.9, we conclude that neither FMP nor Kripke completeness is
preserved under the map L 7! Lu .
Another interesting way of adding to fusions new axioms mixing the
necessity operators is to use the so called inductive (or Segerberg's) axioms.
First, we extend the language LI with m necessity operators by introducing
the operators E and C and then let
ind = fEp $ 2ip Cp ! ECp C(p ! Ep) ! (p ! Cp)g:

^

i2I
Now, given L 2 NExtKm , we put

LECm = (L & KE & S4C )  ind

where KE and S4C are just K and S4 in the languages with E and C, respectively. The following proposition explains the meaning of the inductive
axioms.
PROPOSITION 2.10 A frame hW R1  : : :  Rm  RE  RC i validates LECm
i hW R1  : : :  Rm i j= L, RE = R1  : : :  Rm and RC is the transitive
reexive closure of RE .
EXAMPLE 2.11 The logic (Alt1  D)EC1 is determined by the frame
h! S i in which S is the successor relation in !. (Here we omit writing RE because RE = S .) For details consult Segerberg 1989].14
No general results are known about the preservation properties of the
map L 7! LECm . In fact, it is easy to extend the counter-examples for the
map L 7! Lu to the present case (see Hemaspaandra 1996]). However, at
least in some cases|especially those that are of importance for epistemic
logic|the logic LECm enjoys a number of desirable properties.
14 Krister Segerberg kindly informed us that this result was independently obtained by
D. Scott, H. Kamp, K. Fine and himself.

ADVANCED MODAL LOGIC

N

N

89

N

THEOREM 2.12 (Halpern and Moses 1992) For every m 1, the logics
m
m
( m
i=1 K)ECm , ( i=1 S4)ECm and ( i=1 S5)ECm have FMP.

Proof We consider only L = (Nmi=1 S5)ECm. The proof is by ltration

and so the main diculty is to nd a suitable \lter". Suppose that ' 62 L
and let M = hhW R1  : : :  Rm  RE  RC i  Ui be the canonical model for L.
Denote by ;: the closure of a set of formulas ; under negations and dene
a lter ' = ':1  ':2  ':3 , where '1 = Sub', '2 = f2i  : E 2 ':1 g
and '3 = fEC 2i C : C 2 ':1 g. Certainly, ' is nite and closed under
subformulas. Now, we lter M through ', i.e., put W = fx] : x 2 W g,
where x] consists of all points that validate the same formulas in ' as x,
and
x]Ri y] i 82i  2 ' ((M x) j= 2i  ! (M y) j= 2i )
RE = R1  : : :  Rm 
and RC is the transitive and reexive closure of RE . A rather tedious
inductive proof shows that hW  R1  : : :  Rm  RE  RC i refutes ' under the
valuation U (p) = fx] : x j= pg, p a variable in '. For details we refer the
reader to Halpern and Moses 1992] and Meyer and van der Hoek 1995].

2

It would be of interest to look for big classes of logics L for which LECm
inherits basic properties of L.

2.3 Simulation

In the preceding section we saw how results concerning logics in NExtK can
be extended to a certain class of polymodal logics. More generally, we may
ask whether|at least theoretically|polymodal logics are reducible to unimodal ones. The rst to attack this problem was Thomason 1974b, 1975c]
who proved that each polymodal logic L can be embedded into a unimodal
logic Ls in such a way that L inherits almost all interesting properties of
Ls . Using this result one can construct unimodal logics with various \negative" properties by presenting rst polymodal logics with the corresponding
properties, which is often much easier. It was in this way that Thomason
1975c] constructed Kripke incomplete and undecidable unimodal calculi.
Kracht 1996] strengthened Thomason's result by showing that his embedding not only reects but also (i) preserves almost all important properties
and (ii) induces an isomorphism from the lattice NExtK2 onto the interval
Sim K  2?], for some normal unimodal logic Sim. Thus indeed, in many
respects polymodal logics turn out to be reducible to unimodal ones.
Below we outline Thomason's construction following Kracht 1996] and
Kracht and Wolter 1997a]. To dene the unimodal \simulation" Ls of a

90

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

1


R1 6R2

F ?

I
@
K
A
A@ -
A 6
A -?Fs

Figure 11.
bimodal logic L, let us rst transform each bimodal frame into a unimodal
one.
So suppose F = hW R1  R2  P i is a bimodal frame. Construct a unimodal
frame Fs = hW s  Rs  P s i|the simulation of F|by taking
W s = W ' f1 2g  f1g
Rs = fhhx 1i  hx 2ii : x 2 W g 
fhhx 2i  hx 1ii : x 2 W g 
fhhx 1i  1i : x 2 W g 
fhhx 1i  hy 1ii : x y 2 W xR1 yg 
fhhx 2i  hy 2ii : x y 2 W xR2 yg
P s = f(X ' f2g)  (Y ' f1g)  Z : X Y 2 P Z f1gg:
This construction is illustrated by Fig. 11. One can easily prove that Fs is a
Kripke (di erentiated, rened, descriptive) frame whenever F is so. Notice
also that if W =  then Fs 
= . Now, given a bimodal logic L, dene the
simulation Ls of L to be the unimodal logic
LogfFs : F j= Lg:
To formulate the translation which embeds L into Ls we require the following formulas and notations:
 = 2?
2 ' = 2( ! ')
 = 32?
2 ' = 2( ! ')
 = : ^ :3
2 ' = 2( ! '):
3 , 3 and 3 are dened dually. Observe that the formula  is true in
Fs only at 1,  is true precisely at the points in the set fhx 1i : x 2 W g,
and  is true at the points fhx 2i : x 2 W g and only at them. Put
ps
= p
(:')s
=  ^ :'s 
s
(' ^  ) = ' s ^  s 
(21 ')s = 2 's 
(22 ')s = 2 2 2 's :
By an easy induction on the construction of ' one can prove

ADVANCED MODAL LOGIC

91

LEMMA 2.13 Let M = hF Vi be a bimodal model, X = fx : x j= g and
let Ms = hFs  Vs i be a model such that Vs (p) \ X = V(p) ' f1g, for all
variables p. Then for every bimodal formula ',
(M x) j= ' i (Ms  hx 1i) j= 's 
M j= ' i Ms j=  ! 's 
F j= ' i Fs j=  ! 's :
Using this lemma, both consequence relations `L and `L can be reduced to
the corresponding consequence relations for Ls .
PROPOSITION 2.14 Let L be a bimodal logic,
and ' a bimodal formula. Then

a set of bimodal formulas

`L ' i  ! s `Ls  ! 's 
`L ' i  ! s `Ls  ! 's 

where  ! s = f ! : 2 s g.

To axiomatize Ls , given an axiomatization of L, we require the following
formulas:
(a)  ! (3 p $ 2 p)  ^ 3 p ! 2 3 p
(b)  ! (3 p $ 2 p)
(c)  ! (3 p $ 2 p)
(d)  ^ p ! 2 2 p  ^ p ! 2 2 p
(e)  ^ 3 p ! 2 2 2 3 p:
Let Sim = K  f(a) : : :  (e)g. Obviously, Fs is a frame for Sim whenever
F is a bimodal frame. Consider now a di erentiated frame F = hW R P i
for Sim which contains only one point where  is true. (Actually, every
rooted di erentiated frame for Sim satises this condition.) Construct a
bimodal frame Fs = hV R1  R2  Qi, called the unsimulation of F, in the
following way. Put V = fx 2 W : x j= g, V = fx 2 W : x j=  g and
U = fx 2 W : x j=  g. Since  _  _  2 K, we have W = V  V  U . It
is not hard to verify using (b) and (c) (and the di erentiatedness of F) that
for every x 2 V there exists a unique x 2 V such that xRx , and for every
y 2 V there exists y 2 V such that yRy . By (d), x = x  . Finally, we
put R1 = R \ V 2 , R2 = fhx yi 2 V 2 : x Ry g and Q = fX \ V : X 2 P g.
It is easily proved that Fs is a bimodal frame. The name unsimulation is
justied by the following lemma.
LEMMA 2.15 For every dierentiated bimodal frame F, (Fs )s 
= F.
Now we have:

92

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 2.16 For every bimodal logic L = K2  ,
Ls = Sim   ! s :
Proof Clearly, Sim   ! s Ls. Assume that the converse inclusion
does not hold. Then there exists a rooted di erentiated F such that F 6j= Ls
but F j= Sim   ! s . By Lemma 2.15, (Fs )s 6j= Ls . By the denition
of Ls , we then conclude that Fs 6j= L. And by Proposition 2.14, we have
(Fs )s 6j=  ! s , from which F 6j=  ! s .
2
s
Given L 2 Sim K  2?], the logic Ls = f' :  ! ' 2 Lg is called the
unsimulation of L.
LEMMA 2.17 If L is determined by a class C of frames in which  is true
only at one point then Ls = LogfFs : F 2 Cg.
We are in a position now to formulate the main result of this section.
THEOREM 2.18 (Kracht 1996) The map L 7! Ls is an isomorphism from
the lattice NExtK2 onto the interval Sim K1  2?]. The inverse map
is L 7! Ls . Both these maps preserve tabularity, (global) FMP, (global)
Kripke completeness, decidability, interpolation, strong completeness, Rand D-persistence, elementarity.
Proof To prove the rst claim it suces to show that (Ls)s = L for every
L 2 Sim K  2?]. That L (Ls )s is clear. Consider the set C of all
di erentiated frames Fs such that F j= L and  is true only at one point in
F. By Lemma 2.17, C characterizes Ls . It is not dicult to show now that
the class fF+s : F 2 Cg is closed under subalgebras, homomorphic images
and direct products so it is a variety. Consequently, C is (up to isomorphic
copies) the class of all di erentiated frames for Ls .
Take a di erentiated frame F for (Ls )s . Then Fs j= Ls . So there exists
Gs 2 C which is isomorphic to Fs . Hence (Fs )s 
= (Gs )s and F j= L, since
G j= L. It follows that Ls is determined by fFs : F 2 Cg whenever L is
determined by C .
The preservation of tabularity, (global) FMP, (global) Kripke completeness, and strong completeness under both maps is proved with the help of
Lemma 2.17 and the observation above. It is also clear that L is decidable
whenever Ls is decidable. For the remaining (rather technical) part of the
proof the reader is referred to Kracht 1996] and Kracht and Wolter 1997a].

2

Besides its theoretical signicance, this theorem can be used to transfer
rather subtle counter-examples from polymodal logic to unimodal logic. For
instance, Kracht 1996] constructs a polymodal logic which has FMP and is
globally Kripke incomplete. By Theorem 2.18, we obtain a unimodal logic
with the same properties.

ADVANCED MODAL LOGIC

93

2.4 Minimal tense extensions
Now let us turn to tense logics which may be regarded as normal bimodal
logics containing the axioms p ! 21 32p and p ! 22 31p. Usually studies
in Tense Logic concern some special systems representing various models of
time, like cyclic time, discrete or dense linear time, branching time, relativistic time, etc. Such systems are discussed in Basic Tense Logic (see also
Gabbay et al. 1994] and Goldblatt 1987]). However, as before our concern
is general methods which make it possible to obtain results not only for this
or that particular system but for wide classes of logics. This direction of
studies in Tense Logic is quite new and actually not so many general results
are available. In this and the next section we consider two natural families
of tense logics|the minimal tense extensions of unimodal logics and tense
logics of linear frames. Our aim is to nd out to what extent the theory
developed for unimodal logics in NExtK and especially NExtK4 can be
\lifted" to these families.
The smallest tense logic K:t is determined by the class of bimodal Kripke
frames hW R R;1i in which R is the accessibility relation for 21 and R;1
for 22 . Frames of this type are known as tense Kripke frames general frames
of the form hW R R;1  P i will be called just tense frames. Notice that not
all unimodal general frames hW R P i can be converted into tense frames
hW R R;1  P i because P is not necessarily closed under the operation

32X = fx 2 W : 9y 2 X xR;1 yg:
For instance, in the frame F of Example 1.7 we have 32f! + 1g = f!g 62 P .
Each normal unimodal logic L = K  ; in the language with 21 gives rise
to its minimal tense extension L:t = K:t  ;. From the semantical point of
view L:t is the logic determined by the class of tense frames hW R R;1  P i
such that hW R P i j= L. The formation of the minimal tense extensions
is the simplest way of constructing tense logics from unimodal ones. Of
\natural" tense logics, minimal tense extensions are, for instance, the logics
of (converse) transitive trees, (converse) well-founded frames, (converse)
transitive directed frames, etc. The main aim of this section is to describe
conditions under which various properties of L are inherited by L:t.
Notice rst that unlike fusions, L:t is not in general a conservative extension of L, witness L = LogF where F is again the frame constructed in
Example 1.7: one can easily check that K4:t L:t. However, if L is Kripke
complete then L:t is a conservative extension of L and so L0 :t = L:t implies
L0 L. This example may appear to be accidental (as the rst examples of
Kripke incomplete logics in NExtK). However, we can repeat (with a slight
modication) Blok's construction of Theorem 1.35 and prove the following

94

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 2.19 If L is a union-splitting of NExtK or L = For, then
L0 :t = L:t implies L0 = L. Otherwise there is a continuum of logics in
NExtK having the same minimal tense extension as L.
It is not known whether there exists L 2 NExtK4 such that L:t is not a
conservative extension of L.
Theorem 2.19 leaves us little hope to obtain general positive results for
the whole family of minimal tense extensions. As in the case of unimodal
logics we can try our luck by considering logics with transitive frames. So in
the rest of this section it is assumed that the unimodal and tense logics we
deal with contain K4 and K4:t, respectively, and that frames are transitive.
But even in this case we do not have general preservation results: Wolter
1996b] constructed a logic L 2 NExtK4 having FMP and such that L:t is
not Kripke complete. However, the situation turns out to be not so hopeless
if we restrict attention to the well-behaved classes of logics in NExtK4,
namely logics of nite width, nite depth and conal subframe logics. First,
we have the following results of Wolter 1996a].
THEOREM 2.20 If L 2 NExtK4 is a logic of nite depth then L:t has
FMP. If L 2 NExtK4 is a logic of nite width then L:t is Kripke complete.
It is to be noted that tense logics of nite depth are much more complex
than their unimodal counterparts. For example, there exists an undecidable
nitely axiomatizable logic containing K4:t  21 21 ? (for details see Kracht
and Wolter 1997a]).
The minimal tense extensions of conal subframe logics were investigated
in Wolter 1995, 1996a].
THEOREM 2.21 If L 2 NExtK4 is a conal subframe logic then
(i) L:t is Kripke complete
(ii) L:t has FMP i L is canonical
(iii) L:t is decidable whenever L is nitely axiomatizable.
Before outlining the idea of the proof we note some immediate consequences for a few standard tense logics.
EXAMPLE 2.22 (i) The logic of the converse well-founded tense frames is
GL:t it does not have FMP but is decidable. (ii) The logic of the converse
transitive trees is K4:3:t it has FMP and is decidable. (iii) The logic of
the converse well-founded directed tense frames is GL:t  K4:2:t it does
not have FMP and is decidable.

Proof The proof of the negative part, i.e., that L:t does not have FMP if

L is not canonical, is rather technical it is based on the characterization of

ADVANCED MODAL LOGIC

95

the canonical conal subframe logics of Zakharyaschev 1996]. The reader
can get some intuition from the following example: neither Grz:t nor GL:t
has FMP. Indeed, the Grzegorczyk axiom

22 (22 (p ! 22 p) ! p) ! p
is refuted in h!  i and so does not belong to Grz:t however, it is valid
in all nite partial orders. The argument for GL:t is similar: take the Lob
axiom in 22 and the frame h! > <i.
We sketch now the proof of the positive part. For a tense Kripke frame
F = hW R R;1 i, let rp be a partial function associating with some clusters
in F one of the frames
h! > <i or h!  i:

We call it a replacement function for F and dene Frp to be the result of
replacing in F all clusters C in the domain of rp by (disjoint copies of) rpC .
Our rst observation is that for each conal subframe logic L, L:t is determined by a set of frames of the form Frp such that F is of nite depth.
Indeed, suppose ' 62 L:t and consider a countermodel M = hF Vi for '
based on a descriptive nitely generated tense frame F = hW R R;1  P i for
L:t. Say that a point x 2 W is non-eliminable (relative to ') if there are a
subformula  of ' and S 2 fR R;1g such that x 2 maxS fy 2 W : y j= g
or x 2 maxS fy 2 W : y j= :g. Denote by We the set of non-eliminable
points in W and construct a new model Me on the frame Fe = hWe  R
We  R;1 We i by taking Ve (p) = V(p) \ We for all variables p in '. Clearly,
the Kripke frame Fe is of nite depth (d(Fe )  2l('), to be more precise). Besides, using Theorem 1.23 one can easily show that (Me  y) j=  i
(M y) j= , for all  2 Sub' and y 2 We . (Note that Theorem 1.23 is applicable in this case, since hW R P i is descriptive whenever W R R;1  P
is descriptive.) Moreover, the R-reduct hWe  R We i of Fe is a conal subframe of the R-reduct hW Ri of the underlying Kripke frame of F. So Fe is
a frame for L:t whenever L is canonical (= D-persistent). However, this is
not so if L is not canonical.





EXAMPLE 2.23 Consider the frame F = hW R R;1  P i, where hW Ri is
the reexive point 1 followed by the chain h! >i and P consists of all
conite sets containing 1 and their complements. Then F j= GL:t but (for
an arbitrary ') Fe contains 1 and so Fe 6j= GL:t.
A rather tedious proof (see Wolter 1996a]) shows, however, that there
exists a replacement function rp for Fe such that Frp
e validates L:t and all
points in clusters from domrp are eliminable relative to R in F. (In the
example above we put rpf1g = h! > <i and 1 is eliminable relative to

96

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

R.) So let us assume that such rp is given and that its domain is empty if
rp rp
L is canonical. Dene a model Mrp
e = (Fe  V ) as follows. First we put
rp
y 2 V (p) whenever y 2 Ve (p) and y 2= domrp. Consider now a cluster
C = fa0 : : :  am;1 g in domrp. Vrp is dened in rpC by unravelling C into
the chain rpC  more precisely, we put
Vrp (p) \ rpC = fmj + i : j < ! ai 2 V(p)g:
Using the fact that domrp contains only R-eliminable points, one can show
by induction that, for every  2 Sub', (Me  y) j=  i (Mrp
e  y ) j=  , if
C (y) does not belong to domrp, and
fn 2 rpC : (Mrp
e  n) j=  g = fmj + i : j < ! (Me  ai ) j=  g

if a cluster C = fa0  : : :  am;1 g is in domrp. Thus Frp
e refutes ', which
proves that L:t is Kripke complete.
To show that all canonical logics L:t do have FMP we reduce Frp
e once
again. Dene an equivalence relation  on We by induction on the R-depth
dR (x) of a point x in Fe . Suppose that dR (x) = dR (y) and  is already
dened for all points of R-depth < dR (x) and put x  y if the following
conditions are satised: (a) x j=  i y j= , for all  2 Sub' (x ' y, for
short), (b) if z is an R-successor of y and C (z ) 6= C (y) then there exists an
R-successor z 0 of x with C (z 0 ) 6= C (x) such that z  z 0 and vice versa, (c)
the cluster C (x) is degenerate i C (y) is degenerate, (d) rpC (x) = rpC (y),
(e) for each z 2 C (x) there exists z 0 2 C (y) such that z ' z 0 and vice
versa.
Let x] denote the equivalence class generated by x. Dene a frame
G = hV S S ;1 i by taking V = fx] : x 2 We g, and x]S y] i there are
x0 2 x] and y0 2 y] such that x0 Ry0 . Since Fe is of nite depth, V is
nite. Moreover, the map x 7! x] is a reduction of the unimodal frame
hWe  R We i to hV S i. It follows that G is a frame for L:t whenever L is
canonical. Dene a valuation in G by putting x] j= p i x j= p, for all
x 2 We and all variables p in '. Then one can show that x] j=  i x j= ,
for all  2 Sub'. So G 6j= ', as required, which means that L:t has FMP.
To prove the decidability of a nitely axiomatizable L:t we rst show its
completeness with respect to a rather simple class of frames.
Dene a replacement function rf for G as follows. For each cluster C in
Fe the set C ] = fx] : x 2 C g is a cluster in G, and moreover, every cluster
in G can be presented in this way. So we put rf C ] = rpC , for all clusters
C ] in G. Notice that by (d), rf is well-dened. It is easily shown now that
rf
rf
the R-reduct of Frp
e is reducible to the R-reduct of G and that G refutes
'. Thus we obtain

ADVANCED MODAL LOGIC

97

LEMMA 2.24 For each conal subframe logic L,

L:t = LogfGrp : Grp j= L:t G nite, rp a replacement function for Gg:
So, to establish the decidability of a nitely axiomatizable L:t it is enough
now to present an algorithm which is capable of deciding, given an rp for a
nite G and ', whether Grp j= '. To this end we require the notion of a
cluster assignment t = ht1  t2 i in a tense frame G, which is any function from
the set of clusters in G into the set fm jg'fm jg such that tC = (m m) if C
is degenerate (here m and j are just two symbols m stands for \maximal"
and j for \joker"). A valuation V in G is called '-good for (G t) if the
following conditions hold:
 if t1 C = j then C \ maxR (V()) = , for all  2 Sub'
 if t2 C = j then C \ maxR 1 (V()) = , for all  2 Sub' .
;

EXAMPLE 2.25 Let F be the frame constructed in Example 2.23 and suppose that tf1g = (j m). Then each valuation V in F is '-good for (G t)
no matter what ' is, because 1 is eliminable relative to R. The point 1
is not R;1 -eliminable, since 1 2 maxR 1 (>).
;

Given a formula ', a nite frame F and a replacement function rp for
F, we construct a nite frame G = hV S S ;1 i with a cluster assignment
t as follows. Let k be the number of variables in '. Then G is obtained
from Frp by replacing every rpC = h! > <i with a non-degenerate cluster
C 0 of cardinality 2k , S -followed by a chain of 2l(') irreexive points, and
by replacing every rpC = h!  i with a non-degenerate cluster C 0 of
cardinality 2k , S -followed by a chain of 2l(') reexive points. The cluster
assignment t in G is dened by putting tC 0 = (j m), for all new clusters
C 0 of cardinality 2k , and tC 0 = (m m), for all the other clusters. It is
not dicult now to prove that Frp j= ' i (G U) j= ', for all '-good for
(G t) valuations U in G. This equivalence provides an e ective procedure
for deciding whether Frp j= '.
2
Note that a similar technique can be used to prove completeness and
decidability of various tense logics that are not minimal tense extensions.
For instance, all logics of the form L:t  3222 p ! 22 32p, where L is a
conal subframe logic, are complete and decidable if nitely axiomatizable.

2.5 Tense logics of linear frames





One of the most important types of tense logics are logics characterized
by linear tense frames, i.e., transitive frames W R R;1  P such that, for

98

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

all x y 2 W , xRy or xR;1 y or x = y. For example, Bull 1968] and
Segerberg 1970] axiomatized the logics of the frames, hZ < >i, hQ  < >i
and hR < >i (Z, Q and R are the sets of integer, rational and real numbers,
respectively).
Linear tense logics form the lattice NExtLin, where



Lin = K4:t  3132p _ 3231p ! p _ 31p _ 32p



is the tense logic determined by the class of all linearly ordered Kripke
frames W R R;1 . As we saw in Section 1.11, even unimodal logics of
linear orders are rather non-trivial (for instance, they do not always enjoy
FMP). Yet they can be characterized by Kripke frames with a transparent structure, which yields a decision algorithm for those of them that are
nitely axiomatizable. Tense logics of linear frames turn out to be even more
complicated. In fact, one can nd almost all kinds of \monsters" among
them: uncountably many logics without Kripke frames, strongly complete
logics that are not canonical, canonical logics that are not R-persistent,
incomplete subframe logics, etc. Nevertheless, in this section we show that
these logics are quite manageable. Our exposition follows Wolter 1996c,d],
where the reader can nd the omitted details. All frames in this section are
assumed to be linear.
Given a nite sequence F = hFi = hWi  Ri  Pi i : 1  i  ni of disjoint
frames, we denote by F] = F1  : : :  Fn the ordered sum of them, i.e., the
frame W R R;1  P in which




n
n
 (Wi ' Wj )
W = Wi  R = Ri 
i=1

i=1

1i<j n

and P = fX1  : : :  Xn : Xi 2 Pi g. Each nite frame can be represented
then as the ordered sum C1  : : :  Cn of its clusters.
We begin our study by developing a language of \canonical formulas" for
axiomatizing logics in NExtLin and characterizing the constitution of their
frames. It will play the same role as the language of canonical formulas for
K4. With every nite frame F = hW R R;1i = C1  : : :  Cn and a cluster
assignment t = (t1  t2 ) in it we associate the formula

(F t) = (F t) ^ 21 (F t) ^ 22 (F t) ! :pr 
where r is an arbitrary xed point in F and
(F t) =

^fpx ! 3 py : xRy :(yRx)g ^
^fpx ! 3 py : xR y :(xRy)g ^
1
2

;1

ADVANCED MODAL LOGIC

^fpx ! :py : x 6= yg ^ ^fpx ! :3 py : :(xRy)g ^
^fpx ! 3 py : 9i  n (t Ci = m ^ x y 2 Ci ^ xRy)g ^
^fpx ! 3 py : 9i  n (t Ci = m ^ x y 2 Ci ^ xR y)g ^
_fpy : y 2 W g:

99

2

1

1

2

2

;1

To explain the semantical meaning of these formulas, notice rst that if
tC = (m m) for all clusters C then G 6j= (F t) i G is reducible to F so
Lin  (F t) is a splitting of NExtLin. Suppose now that tiC = j for some
i 2 f1 2g and some cluster C in F. In this case G 6j= (F t) i there exist
frames Gi , for 1  i  n, such that G = G1  : : :  Gn and Gi 6j= (Ci  t Ci )
for all 1  i  n. So it suces to examine the situation when G 6j= (C t)
for a cluster C . Assume for simplicity that G is a Kripke frame. Case 1:
tC = (j j). Then G 6j= (C t) i jGj jC j. Case 2: tC = (m j). Then C is
non-degenerate and G 6j= (C t) i either G contains an R-nal cluster of
cardinality jC j or it has no R-nal point at all. Case 3: tC = (j m). This
is the mirror image of Case 2. Case 4: tC = (m m). If C is an irreexive
point then G is an irreexive point as well whenever G 6j= (C t). If C is
non-degenerate and G 6j= (C t) then G satises the conditions of Cases 2
and 3.
EXAMPLE 2.26 Let  = (a-b t) where ta = (m j) and tb = (j m).
Then F 6j=  i there exists a non-empty upward closed set X 2 P such
that 8x 2 X 9y 2 X yRx, W ; X 6=  and 8px 2 W ; X 9y 2 W ; X xRy.
Hence hQ  < >i 6j=  (take X = fy 2 Q : 2 < yg) but hR < >i j= ,
since the real line contains no gaps.
THEOREM 2.27 There is an algorithm which, given a formula ', returns
formulas (F1  t1 ) : : :  (Fn  tn ) such that
Lin  ' = Lin  (F1 t1 )  : : :  (Fn tn ):
Proof Let (Fi  ti), 1  i  n, be the collection of all nite frames with type
assignments such that, for each i, (a) there is a countermodel Mi = hFi  Vi i
for ' in which Vi is '-good for (Fi  ti ), (b) the depth of Fi does not exceed
4l(') + 1, and (c) no cluster in Fi contains more than 2v(') points, where
v(') is the number of variables in '.
Let F refute (Gi  ti ) under a valuation U. By the denition of (Fi  ti ),
the model Mi refutes '. Dene a valuation U0 in F by taking, for all variables
p in ',
U0 (p) = fU(px) : x 2 Vi (p)g:
It is not hard to show by induction that U0 () = fU(px) : x 2 Vi ()g
for all  2 Sub', and so F refutes ' under U0 . Thus F j= ' implies



S

100

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Ordt = Logfh < >i :  an ordinalg =
Lin  (; ( (j m)))
Et
= Lin  31>  32> =
Lin  (; ( (m m)))  (( (m m)) ;)
On = Logh!n < >i =
Ordt  ((| (m j))  :{z: :  ( (m j)))} (; ( (m m)))

RD
LD
Zt

Dsn
Qt
Rt
Rdt

n+1

= LogfG : 8x(:xRx ! 9y(xRy ^ fz : xRzRyg = ))g =
Lin  (; ( (m m)))  (; ( (m m))  ( (m j)))
= the mirror image of RD
= LoghZ < >i =
RD  LD  (( (j j))  ( (j m)))
(( (m j))  ( (j j)))
= Lin  2n1 +1 p ! 2n1 p =
Lin  (; ( (m m)  : : :  ( (m m)) ;)

|

{z

n+1

= LoghQ  < >i =
Ds1  Et
= LoghR < >i =
Qt  (( (m j))  ( (j m)))
= Logfh  i :  an ordinalg =
Lin  (; (#2  (j m)))

}

Table 3. Axiomatizations of standard tense logics

F j= (Fi  ti ) for every i. The converse direction is rather technical we
refer the reader to Wolter 1996d].
2
\Canonical" axiomatizations of some standard linear tense logics are
shown in Table 3, where we use the following abbreviations. Given a nite frame F = C1  : : :  Cn , we write ((C1  tC1 )  : : :  (Cn  tCn ))
instead of (F t) and (; (C1  tC1 )  : : :  (Cn  tCn )) instead of

((C1  tC1 )  : : :  (Cn  tCn ))  (( (j j))  (C1  tC1 )  : : :  (Cn  tCn )):
((C1  tC1 )  : : :  (Cn  tCn ) ;) is dened analogously.
T
Now we exploit the formulas (F t) to characterize the -irreducible

ADVANCED MODAL LOGIC

101

logics in NExtLin. Recall that every logic L 2 NExtL0 is represented as

\

L = fL0  L : L0 is

\ -irreducibleg:
T

So such a characterization can open the door to a better understanding of
the structure of the lattice NExtLin. The -irreducible logics will be described semantically as the logics determined by certain descriptive frames.
DEFINITION 2.28 (1) Denote by #
k the non-degenerate cluster with k > 0
points.
(2) Let !< (0) be the strictly ascending chain h! < >i of natural numbers, !<(1) the chain h!  i, !< (2) the ascending chain of natural numbers in which precisely the even points are reexive, !< (3) the chain in
which precisely the multiples of 3 are reexive, and so on !> (n) is the
mirror image of !< (n).
(3) C(0 #
1 ) is the mirror image of the frame introduced in Example 2.23,
i.e., C(0 #
1 ) = h! < (0)  #
1  P i, where P consists of all conite sets containing #
1 and their complements. We generalize this construction to chains
!< (n) and clusters #k . Namely, for n < !, k > 1 and #k = fa0  : : :  ak;1 g,
we put
C(n #k ) = h!< (n)  #k  P i
where P is the set of possible values generated by fXi : 0  i  k ; 1g, for
Xi = fai g  fkj + i : j 2 !g, 0  i  k ; 1. C(#k  n) denotes the mirror
image of C(n #
k ).
(4) C(0 #
1  0) = h! < (0)  #
1  ! > (0) P i, where P consists of all conite
sets containing #
1 and their complements.
It is easy to check that the frames dened in (3) and (4) are descriptive
and a singleton fxg is in P i x 62 #
k.
For a class of frames C , we denote by C the class of nite sequences of
frames from C and let C ] = fF] : F 2 C g. The class of nite clusters
and the frames of the form (3) in Denition 2.28 is denoted by B0  put also
B = fC(0 #
1  0)g  B0 .
THEOREM 2.29 Each logic L 2 NExtLin is determined by a set C B ].
If L is nitely axiomatizable then L = LogC for some set C B0 ].
Proof We explain the idea of the proof of the rst claim. Suppose that
M = hF Vi is a countermodel for  = ((C1  tC1 )  : : :  (Cn  tCn )) based
on a descriptive frame F = hW R R;1 P i. We must show that there exists
G 2 B ] refuting  and such that LogG  LogF. Consider the sets

_

Wi = fy 2 W : (M y) j= fpx : x 2 Ci gg:

102

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

One can easily show that Wi are intervals in F and F = F1  : : :  Fn , for
the subframes Fi of F induced by Wi . Moreover, G = G] is as required
if G = hG1  : : :  Gn i is a sequence in B such that LogGi  LogFi , and
Gi 6j= (Ci  tCi ), for 1  i  n. Frames Gi with those properties are
constructed in Wolter96d].
2
EXAMPLE 2.30 The logic Qt is determined by the frames F 2 B ] which
contain no pair of adjacent irreexive points, and Rt is determined by the
frames F 2 B ] which contain neither a pair of adjacent irreexive points
nor a pair of adjacent non-degenerate clusters.

T

It is not dicult to show now that the logics LogF, for F 2 B ], coincide
with the -irreducible logics in NExtLin. Our rst aim is achieved, and
in the remaining part of this section we shall draw consequences of this
result. Using the same sort of arguments as in the proof of Theorem 2.21
and Kruskal's 1960] Tree Theorem one can prove
COROLLARY 2.31 (i) All nitely axiomatizable logics in NExtLin are decidable.
(ii) A logic L is nitely axiomatizable whenever there exists n < ! such
that L 2 NExtDsn .
It follows in particular that all logics in NExtQt and all logics of reexive
frames are nitely axiomatizable and decidable.
Now we formulate two corollaries concerning the Kripke completeness of
linear tense logics. First, it is not hard to see that every logic in NExtLin
characterized by an innite frame in B ] is Kripke incomplete. Using this
observation one can prove
COROLLARY 2.32 Suppose L 2 NExtLin and there is a Kripke frame of
innite depth for L. Then there exists a Kripke incomplete logic in NExtL.
This result means in particular that in Tense Logic we do not have analogues of the unimodal completeness results of Bull 1966b] and Fine 1974c].
However, if a logic is complete then it is determined by a simple class of
frames. Let K be the class frames containing nite clusters and frames of
the form (2) in Denition 2.28.
THEOREM 2.33 Each Kripke complete logic in NExtLin is determined by
a subset of K ].
One of the main types of logics considered in conventional Tense Logic
are logics determined by strict linear orders, known also as time-lines. We
call them t-line logics. All logics in Table 3, save Rdt , are t-line logics.

ADVANCED MODAL LOGIC

103

T-line logics were dened semantically, and now we are going to determine
a necessary syntactic condition for a linear tense logic to be a t-line logic.
Given a frame F, we denote by F the frame that results from F by
replacing its proper clusters with reexive points. Call L 2 NExtLin a
t-axiom logic if L is axiomatizable by a set of formulas of the form (F t)
in which F contains no proper clusters.
PROPOSITION 2.34 The following conditions are equivalent for all logics
L 2 NExtLin:
(i) L is a t-axiom logic
(ii) F j= L implies F j= L, for every F 2 B ].
(iii) (G t) 2 L implies (G  t) 2 L,15 for every nite G.

Proof The implications (i) ) (ii) and (iii) ) (i) are clear. To prove that
(ii) ) (iii), suppose (G  t) 62 L. Then there exists a frame F 2 B ] for L
refuting (G  t). Without loss of generality we may assume that F contains
no proper clusters. By enlarging some clusters in F we can construct a frame
H 2 B ] such that H = F and H 6j= (G t). In view of (ii), H j= L and so
(G t) 62 L.
2
It follows that the t-axiom logics form a complete sublattice of the lattice
NExtLin.
THEOREM 2.35 (i) All nitely axiomatizable t-axiom logics are Kripke
complete.
(ii) All t-line logics are t-axiom logics.

Proof (i) Suppose that L = Lin  f(Gi  ti ) : i 2 I g, for some nite set

I . By Theorem 2.29, L is determined by a subset of B0 ]. For F 2 B0 ],
let kF be the Kripke frame that results from F by replacing all C(n #
k)
<
>
and C(#
k  n) with ! (n) and ! (n), respectively. Then we clearly have
LogkF LogF, and F j= (G  t) i kF j= (G  t). It follows that L is
Kripke complete. (ii) Suppose that L is a t-line logic. By Proposition 2.34
(3), it suces to observe that F j= (G  t) i F j= (G t), for all time-lines
F and all nite G.
2
So the fact that in Table 3 all t-line logics are axiomatized by canonical formulas of the form (G  t) is no accident. Finding and verifying
axiomatizations of t-line logics becomes almost trivial now.
EXAMPLE 2.36 Let us check the axiomatization of Zt in Table 3. Put
L = RD  LD  (( (j j))  ( (j m)))  (( (m j))  ( (j j))):
15 We assume that tC = t whenever  replaces C in G.

104

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

By Theorem 2.35, L is complete. By Theorem 2.33, L is then determined by
a subset of K ]. Clearly this set contains hZ < >i, possibly #
k for k > 0,
and nothing else. But the logic of #
k contains Zt , for all k > 0.
We conclude this section by discussing the decidability of properties of
logics in NExtLin. In Section 4.4 it will be shown that almost all interesting
properties of calculi are undecidable in NExtK and even in NExtS4. In
NExtLin the situation is di erent, as was proved in Wolter 1996d, 1997d].
THEOREM 2.37 (i) There are algorithms which, given a formula ', decide
whether Lin  ' has FMP, interpolation, whether it is Kripke complete,
strongly complete, canonical, R-persistent.
(ii) A linear tense logic is canonical i it is D-persistent i it is complete
and its frames are rst order denable.
(iii) If a logic in NExtLin has a frame of innite depth then it does not
have interpolation.
So NExtLin provides an interesting example of a rather complex lattice
of modal logics for which almost all important properties of calculi are
decidable. We shall not go into details of the proof here but discuss quite
natural criteria for canonicity and strong completeness of logics in NExtLin
required to prove this theorem. Denote by B+ the class of frames containing
B together with frames C(n1  #
k  n2 ) dened as follows. Suppose k > 1,
n1  n2 < ! are such that n1 + n2 > 0 and #k = fa0  : : :  ak;1 g. Then

C(n1  #k  n2 ) = h!< (n1 )  #k  !> (n2 ) P i
where P is the set of possible values generated by fXi : 0  i  k ; 1g, for
Xi = fai g  fkj + i : j 2 !g  fk j + i : j 2 !g
and f0  1  : : :  n  : : :g being the points in !>(n2 ).
Let F be the class of frames of the form
hf0 : : :  n1 g < >i  #
1  hf0 : : :  n2 g < >i or hf0 : : :  ng < >i :
THEOREM 2.38 (i) A logic L 2 NExtLin is canonical i the underlying
Kripke frame of each frame F 2 B+ ] for L validates L as well.
(ii) A logic L 2 NExtLin is strongly complete i for each frame F 2 B+]
validating L, there exists a Kripke frame G for L which results from F by
replacing
 every C(n #
k ) with ! < (n) or ! < (n)  H  #
k , for some H 2 F , and

 every C(#
k  n) with ! > (n) or #
k  H  ! > (n), for some H 2 F , and

ADVANCED MODAL LOGIC

105

 every C(n1  #
k  n2 ) with ! < (n1 )  H  ! > (n2 ), for some H 2 F .

EXAMPLE 2.39 The logic Rt is not canonical because C(2 #
2 ) j= Rt but
!< (2)  #2 6j= Rt . However, Rt is strongly complete, since F j= Rt whenever
G 2 B+] validates Rt and F is obtained from G as in the formulation of
Theorem 2.38 with H =  2 F .
One can also use Theorem 2.38 to construct two strongly complete logics

L1  L2 2 NExtLin whose sum L1  L2 is not strongly complete (see Wolter

1996c]).

2.6 Bimodal provability logics
Bimodal provability logics emerge when combinations of two di erent provability predicates are investigated, for example, if 21 is understood as \it
is provable in PA" and 22 as \it is provable in ZF". In contrast to the
situation in unimodal provability logic, where almost all provability predicates behave like the necessity operator 2 in GL, there exist quite a lot
of di erent types of bimodal provability logics. Various completeness results extending Solovay's completeness theorem for GL to the bimodal case
were established by Smorynski 1985], Montagna 1987], Beklemishev 1994,
1996] and Visser 1995]. Here we will not deal with the interpretation of
modal operators as provability predicates but sketch some results on modal
logics containing the bimodal provability logic

CSM0 = (GL & GL)  21p ! 22 p  22p ! 2122 p
(named so by Visser 1995] after Carlson, Smorynski and Montagna). A
number of provability logics is included in this class, witness the list below.
(As in unimodal provability logic we have quasi-normal logics among them,
i.e., sets of formulas containing K2 and closed under modus ponens and
substitutions (but not necessarily under '=2i '). Recall that we denote by
L + ; the smallest quasi-normal logic containing L and ;.)
 CSM1 = CSM0  22 (21 p ! p). (This is PRLZF in Smorynski
1985] and F in Montagna 1987].)
 NB1 = CSM0  (:21 p ^ 22 p) ! 22 (21 q ! q).

 CSM2 = CSM1 + 21 p ! p. (This is PRLZF + Reection21 in
Smorynski 1985] and F1 in Montagna 1987].)

 CSM3 = CSM2 + 22 p ! p. (This is PRLZF + Reection22 in
Smorynski 1985].)

106

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

 NB2 = NB1 + 22 p ! p + 22 p ! 21 p.

A remarkable feature of CSM0 is that|like in GL|we have uniquely determined denable xed points.
THEOREM 2.40 (Smorynski 1985) Let '(p) be a formula in which every
occurrence of p lies within the scope of some 21 or some 22 . Then
(i) there exists a formula  containing only the propositional variables of
'(p) dierent from p such that  $ '() 2 CSM0 
(ii) 21 ((p $ '(p)) ^ (q $ '(q))) ! (p $ q) 2 CSM0 .
In the remaining part of this section we are concerned with subframe
logics containing CSM0 , the main result stating that those of them that
are nitely axiomatizable are decidable. All the provability logics introduced
above turn out to be subframe logics, so we obtain a uniform proof of their
decidability. An interesting trait of subframe logics in ExtCSM0 is that
(as a rule) they are Kripke incomplete in the list above such are CSMi ,
i = 1 2 3, and NBi , i = 1 2. The proof extends the techniques introduced
by Visser 1995] for details we refer the reader to Wolter 1997a].
First we develop|as was done for NExtK4 and NExtLin|a frame theoretic language for axiomatizing subframe logics in the lattice ExtCSM0 .
A nite frame G = hW R1  R2 i validates CSM0 i both R1 and R2 are
transitive, irreexive, R2 R1 and
8x y z (xR1 y ^ yR2 z ! xR2 z ):

In this section all (not only nite) frames are assumed to satisfy these conditions, save irreexivity.
A nite frame F is called a surrogate frame if it has precisely one root
r and all points di erent from r are R2 -irreexive. Surrogate frames will
provide the language to axiomatize subframe logics in ExtCSM0 . A normal
surrogate frame hW R1  R2 i is a surrogate frame in which the root r is
R1 -irreexive. We write xRip y i xRi y and :yRi x. Given a frame G =
hV S1  S2  Qi for CSM0 and a surrogate frame F = hW R1  R2 i, a map h
from V onto W is called a weak reduction of G to F if for i 2 f1 2g and all
x y 2 V ,
 xSi y implies f (x)Ri f (y),
 f (x)Rip f (y) implies 9z 2 V (xSi z ^ f (z ) = f (y)),
 f ;1(X ) 2 Q for all X W .
(The standard denition of reduction is relaxed here in the second condition.) Each weak reduction to a CSM0 -frames is a usual reduction, since in

ADVANCED MODAL LOGIC

107

this case Rip = Ri . A frame G is said to be weakly subreducible to a surrogate frame F if a subframe of G is weakly reducible to F. To describe weak
subreducibility syntactically, with each surrogate frame F = hW R1  R2 i we
associate the formula
(F) = (F) ^ 21 (F) ! :pr 
where r is the root of F and
(F) =
fpx ! 31py : xR1p y x y 2 W g ^
fpx ! 32py : xR2p y x y 2 W g ^
fpx ! :py : x 6= y x y 2 W g ^
fpx ! :31 py : :(xR1 y) x y 2 W g ^
fpx ! :32 py : :(xR2 y) x y 2 W g:

^
^
^
^
^

LEMMA 2.41 For every surrogate frame F and every CSM0 -frame G, G 6j=
(F) i G is weakly subreducible to F.
It follows immediately that CSM0  (F) and CSM0 + (F) are subframe
logics. Conversely, we have the following completeness result.
THEOREM 2.42 (i) There is an algorithm which, given a formula ' such
that CSM0 + ' is a subframe logic, returns surrogate frames F1  : : :  Fn for
which
CSM0 + ' = CSM0 + (F1) + : : : + (Fn):
(ii) There is an algorithm which, given a formula ' such that CSM0  '
is a subframe logic, returns normal surrogate frames F1  : : :  Fn such that
CSM0  ' = CSM0  (F1)  : : :  (Fn):
Table 4 shows axiomatizations of the logics introduced above by means of
formulas of the form (F). In this section we adopt the convention that in
gures we place the number 1 nearby an arrow from x to y if xR1 y and
:xR2 y. An arrow without a number means that xR2 y (and therefore xR1 y
as well).
The proof of decidability is based on the completeness of subframe logics
in ExtCSM0 with respect to rather simple descriptive frames. With every
surrogate frame F we associate a nite set of frames E(F) = fFA : A 2
SeqFg. Loosely, it is dened as follows. Let us rst assume that the root r
of F is R2 -irreexive. Then the frames in E(F) are the results of inserting an
innite strictly descending R1 -chain, denoted by C (!), between each nondegenerate R1 -cluster C and its R1 -successors. This denes R1 uniquely.

108

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

CSM1
CSM0 + 21p ! p
CSM0 + 22p ! p


= CSM0  ( 6)
= CSM0 + ()

= CSM0 + ( 1 )
1
CSM0 + 22p ! 21 p = CSM0 + ( 61 )
 1-


I
@

;
I
@

;
1
1
@
;
@
;
NB1
= CSM0  (  )  (  )
 1-
 -
I
@

;
I ;
@

1
( @; )  ( @;1 )
Table 4. Axiomatizations of provability logics
However, R2 may be dened in di erent ways, since a point R2 -seeing a
point in C need not (but may) R2 -see certain points in the chain C (!).
To be more precise, the set SeqF consists of all sequences A of the form

A = hAx : xR1 x x 2 W i.
where Ax is a subset of fy 2 W ; C : yR2 xg such that for all y and z ,
y 2 Ax and zR1y imply z 2 Ax . For each non-degenerate R1 -cluster C ,
denote by C (!) the set f(n C ) : n 2 !g. Finally, given A 2 SeqF, we
construct FA = hV S0  S1 i as the frame satisfying the following conditions:
 V = W  fC (!) : C a non-degenerate R1 -cluster in Fg
 Ri = Si \ (W ' W ), for i 2 f1 2g
 S1 is dened so that C (!) becomes an innite descending chain between C and its immediate successors
 for every non-degenerate R1 -cluster C ,
{ ((C (!)  C ) ' (C (!)  C )) \ S2 = ,
{ for all y 2 W ; C and x 2 C (!), xS2y i CR2y,
{ for all y 2 W ; C , C = fj : 0  j  m ; 1g and x 2 C (!), yS2x
i 9i 2 !9j  m ; 1 (x = (im + j C ) ^ y 2 Aj ),
{ for all x 2 C (!) and y 2 V ; C , xS2y i CS2y.
We illustrate this technical denition by a simple example.

S

ADVANCED MODAL LOGIC



6



6



6

c 1-d





..
.
 1-







6 6

a

(a)

b

6 6



(b)

109
-
6



6
-
6


..
.
1
-

6 6





(c)

Figure 12.
EXAMPLE 2.43 Construct E(F) for the frame F in Fig. 12 (a). In this
case we have two R1 -reexive points, namely c and d. So, SeqF consists of
pairs hAc  Ad i. There are four di erent pairs and so we have four frames
in E(F): the frame in Fig. 12 (b) is Fhi and that in (c) is Fhfagfbgi.
Fhfbgi is obtained from Fhfagfbgi by omitting the R2 -arrows starting from
a, save the arrow to c, and Fhfagi is obtained from Fhfagfbgi by omitting
the R2 -arrows starting from b, save the arrow to d.
Suppose now that the root r of F = hW R1  R2 i is R2 -reexive. We dene
FA as in the previous case, but this time we also insert an innite strictly
descending R2 -chain C (!) between r and its R1 -successors.
We have dened the relational component of our frames and now turn to
their sets of possible values. Given FA = hV S1  S2 i and a non-degenerate
R1 -cluster C = fj : 0  j  m ; 1g in F, let
PC = ffj g  f(im + j C ) : i 2 !g : j = 0 : : :  m ; 1g
and denote by P the closure of
ffxg : x 2 V :xS1 xg  fPC : C is a non-degenerate R1 -cluster in Fg
under intersections and complements in V . The resultant general frame is
denoted by G(FA ) = hV S1  S2  P i. One can check that it is a descriptive
frame for CSM0 . The following completeness result is proved similarly to
that in Section 2.4.
THEOREM 2.44 (i) Each subframe logic in NExtCSM0 is determined by
a set of frames of the form G(FA ), in which F is a normal surrogate frame
and A 2 SeqF.

110

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV





(ii) Each subframe logic in ExtCSM0 is determined by a set of frames
with distinguished worlds of the form G(FA ) r in which F is a surrogate
frame with root r and A 2 SeqF.
As a consequence of Theorem 2.44 and the fact that, for each surrogate
frame F with root r and each A 2 SeqF, both the logics of G(FA ) and
G(FA ) r are decidable, we obtain
THEOREM 2.45 All nitely axiomatizable subframe logics in ExtCSM0
are decidable.
We conjecture that the method above can be extended to logics without
the GL-axioms, i.e., all nitely axiomatizable subframe logics containing
(K4 & K4)  21 p ! 22 p  22 p ! 21 22 p are decidable.





3 SUPERINTUITIONISTIC LOGICS
Although C.I. Lewis constructed his rst modal calculus S3 in 1918, it
was Godel's 1933] two page note that attracted serious attention of mathematical logicians to modal systems. While Lewis 1918] used an abstract
necessity operator to avoid paradoxes of material implication, Godel 1933]
and earlier Orlov 1928]16 treated 2 as \it is provable" to give a classical interpretation of intuitionistic propositional logic Int by means of embedding
it into a modal \provability" system which turned out to be equivalent to
Lewis' S4.
Approximately at the same time Godel 1932] observed that there are
innitely many logics located between Int and classical logic Cl, which|
together with the creation of constructive (proper) extensions of Int by
Kleene 1945] and Rose 1953] (realizability logic), Medvedev 1962] (logic
of nite problems), Kreisel and Putnam 1957]|gave an impetus to studying the class of logics intermediate between Int and Cl, started by Umezawa
1955, 1959]. Godel's embedding of Int into S4, presented in an algebraic
form by McKinsey and Tarski 1948] and extended to all intermediate logics
by Dummett and Lemmon 1959], made it possible to develop the theories
of modal and intermediate logics in parallel ways. And the structural results
of Blok 1976] and Esakia 1979a,b], establishing an isomorphism between
the lattices ExtInt and NExtGrz, along with preservation results of Maksimova and Rybakov 1974] and Zakharyaschev 1991], transferring various
properties from modal to intermediate logics and back, showed that in many
respects the theory of intermediate logics is reducible to the theory of logics
in NExtS4.
16 Orlov's paper remained unnoticed till the end of the 1980s. It is remarkable also for
constructing the rst system of relevant logic.

ADVANCED MODAL LOGIC

For
Cl
SmL
KC
LC
SL
KP
BDn

=
=
=
=
=
=
=
=

Int + p
Int + p _ :p
Int + (:q ! p) ! (((p ! q) ! p) ! p)
Int + :p _ ::p
Int + (p ! q) _ (q ! p)
Int + ((::p ! p) ! :p _ p) ! :p _ ::p
Int + (:p ! q _ r) ! (:p ! q) _ (:p ! r)
Int + bdn, where

BWn
BTWn
Tn
Bn
NLn

=
=
=
=
=

Int + Vni=0(pi ! j6=i pj )
Wni=0(:pi ! Wj6=i :pj )
Int + V0i<jn :(W:pi ^ :pj ) !
Int + Vni=0((pi ! Wi6=j pj ) ! WWi6=j pj ) ! Wni=0 pi
Int + ni=0(:pi $ i6=j pj ) ! ni=0 pi
Int + nf n, where

111

bd1 = Wp1 _ :p1  bdWn+1 = pn+1 _ (pn+1 ! bdn)

nf 0 = ?, nf 1 = p, nf 2 = :p, nf ! = >
nf 2m+3 = nf 2m+1 _ nf 2m+2,
nf 2m+4 = nf 2m+3 ! nf 2m+1

Table 5. A list of standard superintuitionistic logics
To demonstrate this as well as some features of intermediate logics is
the main aim of this part. We will use the same system of notations as
in the modal case. In particular, ExtInt is the lattice of all logics of the
form Int + ; (where ; is an arbitrary set of formulas in the language of
Int and + as before means taking the closure under modus ponens and
substitution) we call them superintuitionistic logics or si-logics for short.
Basic facts about the syntax and semantics of Int and relevant references
can be found in Intuitionistic Logic. A list of some \standard" si-logics is
given in Table 5.

3.1 Intuitionistic frames
As in the case of modal logics, the adequate relational semantics for si-logics
can be constructed on the base of the Stone representation of the algebraic
\models" for Int, known as Heyting (or pseudo-Boolean) algebras. It is hard
to trace now who was the rst to introduce intuitionistic general frames|the
earliest references we know are Esakia 1974] and Rautenberg 1979]|but in
any case, having at hand Jonsson and Tarski 1951] and Goldblatt 1976a],
the construction must have been clear.

112

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

An intuitionistic (general) frame is a triple F = hW R P i in which R is a
partial order on W 6=  and P , the set of possible values in F, is a collection
of upward closed subsets (cones) in W containing  and closed under the
Boolean \, , and the operation ( (for !) dened by

X ( Y = fx 2 W : 8y 2 x" (y 2 X ! y 2 Y )g:
If P contains all upward closed subsets in W then we call F a Kripke frame
and denote it by F = hW Ri. An important feature of intuitionistic models
M = hF Vi (V, a valuation in F, maps propositional variables to sets in P )
is that V('), the truth-value of a formula ', is always upward closed.
Every intuitionistic frame F = hW R P i gives rise to the Heyting algebra
F+ = hP \  ( i called the dual of F. Conversely, given a Heyting algebra
A = hA ^ _ ! ?i, we construct its relational representation A+ = hW Ri
by taking W to be the set of all prime lters in A (a lter r is prime if it
is proper and a _ b 2 r implies a 2 r or b 2 r), R to be the set-theoretic
inclusion and
P = ffr 2 W : a 2 rg : a 2 Ag:
It is readily checked that A+ , the dual of A, is an intuitionistic frame,
A
= (A+ )+ and A+ is di erentiated, tight in the sense that

xRy i 8X 2 P (x 2 X ! y 2 X )
and compact, i.e., for any families X

P and Y fW ; X : X 2 P g,

\(X  Y ) = fx 2 W : 8X 2 X 8Y 2 Y (x 2 X ^ x 2 Y )g 6= 
T
whenever (X  Y ) 6=  for every nite subfamilies X
X, Y

Y.
Frames with these three properties (actually di erentiatedness follows from
tightness) are called descriptive. In the same way as in the modal case
one can prove that F is descriptive i F 
= (F+ )+ . Duality between the
basic truth-preserving operations on algebras and descriptive frames (the
denitions of generated subframes, reductions and disjoint unions do not
change) is also established by the same technique.
Since every consistent si-logic L is characterized by its Tarski{Lindenbaum algebra AL, we conclude that L is characterized also by a class of intuitionistic frames, say by the dual of AL.
Rened nitely generated frames for Int look similarly to those for K4:
the only di erence is that now all clusters are simple and the truth-sets must
be upward closed. Fig. 13 showing (a) the free 1-generated Heyting algebra
AInt (1) and (b) its dual FInt(1) will help the reader to restore the details.
AInt (1) was rst constructed by Rieger 1949] and Nishimura 1960] it is
called the Rieger{Nishimura lattice. The formulas nf n dened in Table 5
0

0

0

0

ADVANCED MODAL LOGIC

113

>

:::







 nf
 9

nf 10@
I
@
;
I
@
;
@
@
;
@ nf
nf 7 
8

;
I
@

;
; @
;
@;
nf 5
nf 6 ;
I
@
@
;
I
@
;
@
@
;
@ nf
nf 3 
4
nf

2

I
@
6
@

4

@ * 3
I
@
6
6
@ @@
6  @ * 5
I
@
6
6
@ @
@
8  @ * 7
I@ @ 6
@
6
10 @ @ 9

@
;
I

;
;
@
;
;
@
;
 1
2
I
@

;
@
;
@;
A
?

nf

(a)

p

* 1
6

F<Int1 (1)

Int (1)



(b)

Figure 13.
and used for the construction are known as Nishimura formulas (see also
Section 3 of Intuitionistic Logic).
At the algebraic level the connection between Int and S4 discovered by
Godel is reected by the fact, established in Mckinsey and Tarski 1946],
that the algebra of open elements (i.e., elements a such that 2a = a) of
every modal algebra for S4 (known as a topological Boolean algebra see
Rasiowa and Sikorski 1963]) is a Heyting algebra and conversely, every
Heyting algebra is isomorphic to the algebra of open elements of a suitable
algebra for S4. We explain this result in the frame-theoretic language.
Given a frame F = hW R P i for S4 (which means that R is a quasiorder on W ), we denote by W the set of clusters in F|more generally,
X = fC (x) : x 2 X g|and put C (x)C (y) i xRy,
P = fX : X 2 P ^ X = 2X g = fX : X 2 P ^ X = X"g:
It is readily checked that the structure F = hW R P i is an intuitionistic frame (for instance, (X ) ( (Y ) = (2(;X  Y ))) we call it the
skeleton of F. The skeleton of a model M = hF Vi for S4 is the intuitionistic
model M = hF Vi, where V(p) = V(2p).
Denote by T the Godel translation prexing 2 to all subformulas of a
given intuitionistic formula.17 By induction on the construction of ' one
17

The translation dened in Godel 1933] does not prex 2 to conjunctions and dis-

114

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

can easily prove the following
LEMMA 3.1 (Skeleton) For every model M for S4, every intuitionistic formula ' and every point x in M,
(M C (x)) j= ' i (M x) j= T ('):
It follows that ' 2 Int implies T (') 2 S4. To prove the converse we
should be able to convert intuitionistic frames F into modal ones with the
skeleton (isomorphic to) F. This is trivial if F is a Kripke frame|we can
just regard it to be a frame for S4, which in view of the Kripke completeness
of both Int and S4, shows that T really embeds the former into the latter,
i.e.,
' 2 Int i T (') 2 S4:
In general, the most obvious way of constructing a modal frame from an
intuitionistic frame F = hW R P i is to take the closure P of P under the
Boolean operations \,  and !. It is well known in the theory of Boolean
algebras (see Rasiowa and Sikorski 1963]) that for every X W , X is in
P i
X = (;X1  Y1 ) \ : : : \ (;Xn  Yn )
for some X1  Y1  : : :  Xn Yn 2 P and n 1. It follows that if X 2 P then
2X = (X1 ( Y1 ) \ : : : \ (Xn ( Yn ) 2 P P
and so P is closed under 2 in hW Ri and P coincides with the set of
upward closed sets in P . Thus, hW R P i is a partially ordered modal
frame we shall denote it by F. Moreover, we clearly have F 
= F. If
M = hF Vi is an intuitionistic model then M = h F Vi is a modal model
having M as its skeleton. So by the Skeleton Lemma,
(M x) j= ' i (M x) j= T (')
for every intuitionistic formula ' and every point x in F.
It is worth noting that if F = hW Ri is a nite intuitionistic Kripke frame
then F is also a Kripke frame. However, for an innite F, F is not in
general a Kripke frame, witness h! i.
The operator  is not the only one which, given an intuitionistic frame F,
returns a modal frame whose skeleton is isomorphic to F. As an example, we
dene now an innite class of such operators. For Kripke frames F = hW Ri
and G = hV S i, denote by F ' G the direct product of F and G, i.e., the frame
hW ' V R ' S i in which the relation R ' S is dened component-wise:
hx1  y1 i (R ' S ) hx2  y2 i i x1 Rx2 and y1 Sy2 :
junctions. However this dierence is of no importance as far as embeddings into logics
in NExtS4 are concerned.

ADVANCED MODAL LOGIC

115

Let 0 < k  !. We will regard k to be the set f0 : : :  k ; 1g if k < ! and
f0 1 : : :g if k = !. Denote by  k an operator which, given an intuitionistic
frame F = hW R P i, returns a modal frame  k F = hkW kR kP i such that
(i) hkW kRi is the direct product of the k-point cluster k k2 and hW Ri
(in other words, hkW kRi is obtained from hW Ri by replacing its every
point with a k-point cluster)
(ii)  k F 
= F
(iii) I ' X 2 kP , for every I k and X 2 P .
For instance, we can take kP to be the Boolean closure of the set
fI ' X : I k X 2 P g:
For a Kripke frame F = hW R UpW i we can, of course, take kP = 2kW
and then  k F = kW kR 2kW .

 





3.2 Canonical formulas

The language of canonical formulas, axiomatizing all si-logics and characterizing the structure of their frames, can be easily developed following
the scheme of constructing the canonical formulas for K4 outlined in Section 1.6 and using the connection between modal and intuitionistic frames
established above. We conne ourselves here only to pointing out the differences from the modal case and some interesting peculiarities details can
be found in Zakharyaschev 1983, 1989] and Chagrov and Zakharyaschev
1997].
Actually, there are two important di erences. First, in the denition of
subreduction of F = hW R P i to G the condition (R3) does not correspond
to the fact that all sets in P are upward closed. We replace it by the
following condition
(R30 )
8X 2 Q f ;1(X )# 2 P ,
where Q = fV ; X : X 2 Qg and P = fW ; X : X 2 P g. For a
completely dened f satisfying (R1) and (R2) the condition (R30 ) is clearly
equivalent to (R3) and so every reduction is also a subreduction. If G is a
nite Kripke frame then (R3') is equivalent to 8z 2 V f ;1 (z )# 2 P . G is
a subframe of F if G is a subframe of F and the identity map on V is a
subreduction of F to G. It is of interest to note that in the intuitionistic case
(conal) subreductions are dual to IC(N)-subalgebras of Heyting algebras
which preserve only implication, conjunction (and negation or ?) but do
not necessarily preserve disjunction.
Second, we have to change the denition of open domains. Now we say
an antichain a (of at least two points) is an open domain in an intuitionistic
model N relative to a formula ' if there ia a pair ta = (;a  a ) such that
;a  a = Sub', ;a !
a 62 Int and

V

W

116

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

:p 1 :q

q

I
@
@

G

:p 2 :r

3

p  :p

r 6

@
@


;
;

;
;

@

;

p ! :q
:p ! :q _ :r @;:
:
0 p ! :r
Figure 14.
  2 ;a i a j=  for all a 2 a.

It is worth noting that in any intuitionistic model every antichain a is open
relative to every disjunction free formula '. Indeed, let ;a be dened by
condition above and a = Sub' ; ;a . It should be clear that  ^  2 ;a
i  2 ;a and  2 ;a . And if  !  2 ;a ,  2 ;a but  2 a then a j= 
for every a 2 a and b 6j=  for some b 2 a, whence b 6j=  ! , which is a
contradiction. It follows that ;a !
a 62 Int.
EXAMPLE 3.2 Let us try to characterize the class of intuitionistic refutation frames for the Weak Kreisel{Putnam Formula

V

W

wkp = (:p ! :q _ :r) ! (:p ! :q) _ (:p ! :r):
First we construct its simplest countermodel it is depicted in Fig. 14, where
by putting a formula to the left (right) of a point we mean that it is true
(not true) at the point. Then we observe that every frame F refuting wkp
is conally subreducible to the frame G underlying this countermodel by
the map f dened as follows:

8> 0
if x j= :p ! :q _ :r, x 6j= (:p ! :q) _ (:p ! :r)
>< 1
if x j= :p ! :q _ :r, x j= :p and x j= q
if x j= :p ! :q _ :r, x j= :p and x j= r
f (x) = > 2
if x j= p or x j= :p ^ :q ^ :r
>: 3
undened otherwise.

However, the conal subreducibility to G is only a necessary condition for
F 6j= wkp, witness the frame having the form of the three-dimensional
Boolean cube with the top point deleted. The reason for this is that the
antichain f1 2g is a closed domain in N: it is impossible to insert a point
a between 0 and f1 2g and extend to it consistently the truth-sets for the
depicted formulas. Indeed, otherwise we would have a j= :p ! :q _ :r,
a 6j= :q _ :r and so a 6j= :p, i.e., there must be a point x 2 a" such that

ADVANCED MODAL LOGIC

117

x j= p, but such a point does not exist. In fact, F 6j= wkp i there is a
conal subreduction of F to G satisfying (CDC) for ff1 2gg.
Now, as in the modal case, with every nite rooted intuitionistic frame
F = hW Ri and a set D of antichains in it we can associate two formulas
 (F D ?) and  (F D), called the canonical and negation free canonical
formulas, respectively, so that G 6j=  (F D ?) (G 6j=  (F D)) i there is a
(conal) subreduction of G to F satisfying (CDC) for D. For instance, if
a0  : : :  an are all points in F and a0 is its root, then one can take
^ ij ^ ^ d ^ ? ! p0
 (F D ?) =
ai Raj

where

ij = (

:

d =
?

d2D

^ pk ! pj ) ! pi
aj Rak
^ ( ^ pk ! pi) ! _ pj 

ai 2W ;d" :ai Rak
n
=
(
pk ! pi ) ! ?:
i=0 :ai Rak

^ ^

aj 2d

 (F D) is obtained from  (F D ?) by deleting the conjunct ? .
THEOREM 3.3 There is an algorithm which, given an intuitionistic ', returns canonical formulas  (F1  D1  ?) : : :   (Fn  Dn  ?) such that
Int + ' = Int + (F1  D1 ?) + : : : + (Fn  Dn ?):
So the set of intuitionistic canonical formulas is complete for ExtInt. If
' is negation free then one can use only negation free canonical formulas.
And if ' is disjunction free then all Di are empty.
Table 6 and Theorem 3.4 show canonical axiomatizations of the si-logics
in Table 5. Using this \geometrical" representation it is not hard to see, for
instance, that SmL, known as the Smetanich logic, is the greatest consistent
extension of Int di erent from Cl it is the logic of the two-point rooted
frame. KC, the logic of the Weak Law of the Excluded Middle, is characterized by the class of directed frames. It is the greatest si-logic containing the
same negation free formulas as Int (see Jankov 1968a]). LC, the Dummett
or chain logic, is characterized by the class of linear frames (see Dummett 1959]). BDn and BWn are the minimal logics of depth n and width
n, respectively (see Hosoi 1967] and Smorynski 1973]). Finite frames for
BTWn contain  n top points Smorynski 1973] and nite frames for Tn
are of branching  n, i.e., no point has more than n immediate successors.

118

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

For

= Int +  ()

= Int +  ( 6)

 
6
KA 
A

= Int +  (  ) +  ( 6)
 
K 
A

= Int +  ( A  ?)
 
K 
A

= Int +  ( A )

6
 
K 
A

= Int +  ] ( A  ?)

Cl
SmL
KC
LC
SL



A

K
1 A2 
I
@

;
@6
;

BDn

1 2 
I 6
@

;
= Int +  ( @;  ff1 2gg ?) +  (
n
..6
.
1
= Int +  ( 60 )

BWn

= Int +  ( @; )

KP



 ff1 2gg ?)

z n}|  {
+1

I ;
@


z n}|  {
+1

I

;
@;
 ?)
BTWn = Int + ( @

z n}|  {
+1

I ;
@


Tn

= Int +  ] ( @; )

Bn

= Int +  ] ( @;  ?)

z n}|  {
+1

I ;
@


Table 6. Canonical axioms of standard superintuitionistic logics

ADVANCED MODAL LOGIC

119

THEOREM 3.4 (Nishimura 1960, Anderson 1972) Every extension L of Int
by formulas in one variable can be represented either as
L = Int + nf 2n = Int +  ] (Hn  ?)
or as
L = Int + nf 2n;1 = Int +  ] (Hn+1  ?) +  ] (Hn+2  ?)
where Hn , Hn+1 , Hn+2 are the subframes of the frame in Fig. 13 generated
by the points n, n +1 and n +2, respectively, and  ] (F ?) is an abbreviation
for  (F D]  ?), D] the set of all antichains in F.
Jankov 1969] proved in fact that logics of the form Int +  ] (F ?) and
only them are splittings of ExtInt. However, not every si-logic is a unionsplitting of ExtInt which means that this class has no axiomatic basis.

3.3 Modal companions and preservation theorems
The fact that the Godel translation T embeds Int into S4 and the relationship between intuitionistic and modal frames established in Section 3.1 can
be used to reduce various problems concerning Int (e.g. proving completeness or FMP) to those for S4 and vice versa. Moreover, it turns out that
each logic in ExtInt is embedded by T into some logics in NExtS4, and for
each logic in NExtS4 there is one in ExtInt embeddable in it.
We say a modal logic M 2 NExtS4 is a modal companion of a si-logic L

if L is embedded in M by T , i.e., if for every intuitionistic formula ',
' 2 L i T (') 2 M:
If M is a modal companion of L then L is called the si-fragment of M
and denoted by M . The reason for denoting the operator \modal logic
7 its si-fragment" by the same symbol we used for the skeleton operator is
!
explained by the following
THEOREM 3.5 For every M 2 NExtS4, M = f' : T (') 2 M g. Moreover, if M is characterized by a class C of modal frames then M is characterized by the class C = fF : F 2 Cg of intuitionistic frames.
Proof It suces to show that f' : T (') 2 M g = LogC . Suppose that
T (') 2 M . Then F j= T (') and so, by the Skeleton Lemma, F j= ' for
every F 2 C , i.e., ' 2 LogC . Conversely, if F j= ' for all F 2 C then, by
the same lemma, T (') is valid in all frames in C and so T (') 2 M .
2
Thus,  maps NExtS4 into ExtInt. The following simple observation
shows that actually  is a surjection. Given a logic L 2 ExtInt, we put
 L = S4  fT (') : ' 2 Lg:

120

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 3.6 (Dummett and Lemmon 1959) For every si-logic L,  L is
a modal companion of L.

Proof Clearly, L  L. To prove the converse inclusion, suppose ' 62 L,
i.e., there is a frame F for L refuting '. Since F 
= F, by the Skeleton
Lemma we have F j=  L and F 6j= T ('). Therefore, T (') 62  L and so
' 62  L.
2
Now we use the language of canonical formulas to obtain a general characterization of all modal companions of a given si-logic L. Our presentation
follows Zakharyaschev 1989, 1991]. Notice rst that for every modal frame
G and every intuitionistic canonical formula  (F D ?), G j= (F D ?) i
G j= (F D ?) and so S4  T ((F D ?)) = S4  (F D ?). The same
concern, of course, the negation free canonical formulas.
THEOREM 3.7 A logic M 2 NExtS4 is a modal companion of a si-logic
L = Int + f (Fi  Di  ?) : i 2 I g i M can be represented in the form

M = S4  f(Fi  Di  ?) : i 2 I g  f(Fj  Dj  ?) : j 2 J g
where every frame Fj , for j 2 J , contains a proper cluster.

Proof (() We must show that for every intuitionistic formula ', ' 2 L

i T (') 2 M . Suppose that ' 62 L and F = hW R P i is a frame separating
' from L. We prove that F separates T (') from M . As was observed
above, F 6j= T (') and F j= (Fi  Di  ?) for any i 2 I . So it remains to
show that F j= (Fj  Dj  ?) for every j 2 J .
Suppose otherwise. Then, for some j 2 J , we have a subreduction f of
to the same proper
F to Fj . Let a1 and a2 be distinct points belonging
cluster in Fj . By the denition of subreduction, f ;1 (a1 ) f ;1(a2 )# and
f ;1 (a2 ) f ;1 (a1 )#, and so there is an innite chain x1 Ry1 Rx2 Ry2 R : : : in
F such that fx1 x2 : : :g f ;1(a1 ) and fy1 y2 : : :g f ;1(a2). And since
R is a partial order, all the points xi and yi are distinct.
Since f ;1 (a1 ) 2 P , there are Xi  Yi 2 P such that

f ;1(a1 ) = (;X1  Y1 ) \ : : : \ (;Xn  Yn ):
And since f ;1 (a1 ) \ f ;1 (a2 ) = , for every point yi there is some number ni
such that yi 2 Xni and yi 62 Yni . But then, for some distinct l and m, the
numbers nl and nm must coincide, and so if, say, yl Rym then xm 62 Ynm and
xm 2 Xnl (for yl Rxm Rym , Xi = Xi ", Yi = Yi "). Therefore, xm 62 f ;1 (a1 ),
which is a contradiction.
The rest of the proof presents no diculties.
2

ADVANCED MODAL LOGIC

121

This proof does not touch upon the conality condition. So along with
canonical formulas in Theorem 3.7 we can use negation free canonical formulas. Thus, we have:

S4 = S4:1 = Dum = Grz = Int
S4:2 = (S4:2  Grz) = KC
S4:3 = (S4:3  Grz) = LC
S5 = (S5  Grz) = Cl:
COROLLARY 3.8 The set of modal companions of every consistent si-logic
L forms the interval



;1 (L) =  L  L  ( )] = fM 2 NExtS4 :  L M  L  Grzg
and contains an innite descending chain of logics.

Proof Notice rst that (F D ?) and (F D) are in Grz i F contains
a proper cluster. So ;1 (L)  L,  L  ( )]. On the other hand, the
si-fragments of all logics inthe interval are the same, namely L. Therefore,
;1(L) =  L  L  ( )]. Now, if L is consistent then () 62 L and so
we have

 L  : : :   L  (Cn)  : : :   L  (C2 )   L  (C1 ) = For
where Ci is the non-degenerate cluster with i points.

2

This result is due to Maksimova and Rybakov 1974], Blok 1976] and
Esakia 1979b].
Thus, all modal companions of every si-logic L are contained
 between the
least companion  L and the greatest one, viz.,  L  ( ), which will be
denoted by L. Using Theorems 3.7 and 1.44, we obtain
COROLLARY 3.9 There is an algorithm which, given a modal formula ',
returns an intuitionistic formula  such that (S4  ') = Int + .
The following theorem, which is also a consequence of Theorem 3.7, describes lattice-theoretic properties of the maps ,  and . Items (i), (ii)
and (iv) in it were rst proved by Maksimova and Rybakov 1974], and (iii)
is due to Blok 1976] and Esakia 1979b] and known as the Blok{Esakia
Theorem.

122

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 3.10 (i) The map  is a homomorphism of the lattice NExtS4
onto the lattice ExtInt.
(ii) The map  is an isomorphism of ExtInt into NExtS4.
(iii) The map  is an isomorphism of ExtInt onto NExtGrz.
(iv) All these maps preserve innite sums and intersections of logics.
Now we give frame-theoretic characterizations of the operators  and .
Note rst that the following evident relations between frames for si-logics
and their modal companions hold:

F j= M i F j= M F j= L i F j= L
F j= L i F j=  L F j= L i  k F j=  L:
THEOREM 3.11 (Maksimova and Rybakov 1974) A si-logic L is characterized by a class C of intuitionistic frames i L is characterized by the
class C = fF : F 2 Cg.
Proof ()) It suces to show that any canonical formula (F D ?) 62 L
is refuted by some frame in C . Since F is partially ordered,  (F D ?) 62 L,
i.e., there is F 2 C refuting  (F D ?) and so F 6j= (F D ?). (() is
straightforward.
2
To characterize  we require
LEMMA 3.12 For any canonical formula (F D ?) built on a quasi-ordered
frame F, (F D ?) 2 S4  (F D ?), where D = fd : d 2 Dg and
d = fC (x) : x 2 dg.
Proof Let G be a quasi-ordered frame refuting (F D ?). Then there is
a conal subreduction f of G to F satisfying (CDC) for D. The map h from
F onto F dened by h(x) = C (x), for every x in F, is clearly a reduction
of F to F. So the composition hf is a conal subreduction of G to F, and
it is easy to verify that it satises (CDC) for D.
2
THEOREM 3.13 A si-logic LSis characterized by a class C of frames i  L
is characterized by the class 0<k<!  k C , where  k C = f k F : F 2 Cg.
Proof ()) As was noted above, if F is a frame for L then  k F is a frame for
 L. So suppose that a formula (F D ?), built on a quasi-ordered frame
F =ShW Ri, does not belong to  L and show that it is refuted by some frame
in 0<k<!  k C . By Lemma 3.12, (F D ?) 62  L and so  (F D ?) 62
L. Hence there is a frame G = hV S Qi in C which refutes  (F D ?).
But then G j=  L and G 6j= (F D ?). Let f be a subreduction
of G to F satisfying (CDC) for D and let k = maxfjC (x)j : x 2 W g.

ADVANCED MODAL LOGIC

123

Dene a partial map h from  k G = hkV kS kQi onto F as follows: if x 2 V ,
y0 2 W , f (x) = C (y0 ) and C (y0 ) = fy0  : : :  yn g then we put h(hi xi) = yi ,
for i = 0 : : :  n. By the denition of  k , for any i 2 f0 : : :  ng we have
h;1 (yi ) = fhi xi : x 2 f ;1 (C (y0 ))g = fig ' f ;1(C (y0 )) 2 kQ:
Now, one can readily prove that h is a conal subreduction of  k G to F
satisfying (CDC) for D. So  k G 6j= (F D ?). (() is obvious.
2
It is worth noting that this proof will not change if we put in it k = !.
COROLLARY 3.14 A logic L 2 ExtInt is characterized by a class C of
frames i  L is characterized by the class  ! C .
The following theorem provides a deductive characterization of the maps
 and .
THEOREM 3.15 For every si-logic L and every modal canonical formula
(F D ?) built on a quasi-ordered frame F,
(i) (F D ?) 2  L i  (F D ?) 2 L
(ii) (F D ?) 2 L i either F is partially ordered and  (F D ?) 2 L
or F contains a proper cluster.
Proof (i) The implication ()) was actually established in the proof of
Theorem 3.13, and the converse one follows from Lemma 3.12.
(ii) Suppose (F D ?) 2 L. Then either F is partially ordered, and so
 (F D ?) 2 L, or F contains a proper cluster. The converse implication
follows from (i) and the fact that (F D ?) 2 Grz for every frame F with
a proper cluster.
2
The results obtained in this section not only establish some structural
correspondences between logics in ExtInt and NExtS4 and their frames,
but may be also used for transferring various properties of modal logics
to their si-fragments and back. A few results of that sort are collected in
Table 7 we shall cite them as the Preservation Theorem. The preservation
of decidability follows from the denition of  and Theorem 3.15. That
 preserves Kripke completeness, FMP and tabularity is a consequence of
Theorem 3.5. The map  preserves Kripke completeness and FMP, since
we can dene  k in Theorem 3.13 so that  k hW Ri = hkW kRi however,
 does not in general preserve the tabularity, because  Cl = S5 is not
tabular. The preservation of FMP and tabularity under  follows from
Theorem 3.11. On the other hand, Shehtman 1980] proved that  does not
preserve Kripke completeness (since  preserves it and Grz is complete,
this means in particular that Kripke completeness is not preserved under
sums of logics in NExtS4). Some other preservation results in Table 7 will
be discussed later. For references see Chagrov and Zakharyaschev 1992,
1997].

124

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Property of logics

Preserved under

Decidability
Kripke completeness
Strong completeness
Finite model property
Tabularity
Pretabularity
D-persistence
Local tabularity
Disjunction property
Hallden completeness
Interpolation property
Elementarity
Independent axiomatizability

Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
No





Yes
Yes
Yes
Yes
No
No
Yes
No
Yes
No
No
Yes
Yes



Yes
No
No
Yes
Yes
Yes
No
No
Yes
No
No
No
Yes

Table 7. Preservation Theorem

3.4 Completeness
In this section we briey discuss the most important results concerning
completeness of si-logics with respect to various classes of Kripke frames.

Kripke completeness That not all si-logics are complete with respect

to Kripke frames was discovered by Shehtman 1977], who found a way
to adjust Fine's 1974b] idea to the intuitionistic case (which was not so
easy because intuitionistic formulas do not \feel" innite ascending chains
essential in Fine's construction see Section 20 of Basic Modal Logic). Note
however that Kuznetsov's 1975] question whether all si-logics are complete
with respect to the topological semantics (see Intuitionistic Logic) is still
open.
As to general positive results, notice rst that the Preservation Theorem
yields the following translation of Fine's 1974c] Theorem on nite width
logics (si-logics of nite width were studied by Sobolev 1977a]).
THEOREM 3.16 Every si-logic of width n (i.e., a logic in ExtBWn  see
Table 5) is characterized by a class of Noetherian Kripke frames of width
 n.
The translation of Sahlqvist's Theorem gives nothing interesting for silogics. A sort of intuitionistic analog of this theorem has been recently

ADVANCED MODAL LOGIC

125

proved by Ghilardi and Meloni 1997]. Here is a somewhat simplied variant
of their result in which p, q, r, s denote tuples of propositional variables
and ,  tuples of formulas of the same length as r and s, respectively.
THEOREM 3.17 (Ghilardi and Meloni 1997) Suppose '(p q r s) is an intuitionistic formula in which the variables r occur positively and the variables s occur negatively, and which does not contain any !, except for
negations and double negations of atoms, in the premise of a subformula of
the form '0 ! '00 . Assume also that (p q) and (p q) are formulas such
that p occur positively in  and negatively in , while q occur negatively in
 and positively in . Then the logic

Int + '(p q (p q) (p q))
is canonical.

The preservation of D-persistence under  (see Zakharyaschev 1996])
and the fact (discovered by Chagrova 1990]) that  L is characterized by an
elementary class of Kripke frames whenever L is determined by such a class
provide us with an intuitionistic variant of the Fine{van Benthem Theorem.
THEOREM 3.18 If a si-logic is characterized by an elementary class of
Kripke frames then it is D-persistent.
As in the modal case, it is unknown whether the converse of this theorem holds. All known non-elementary si-logics, for instance the Scott logic
SL and the logics Tn of nite n-ary trees (see Rodenburg 1986]) are not
canonical and even strongly complete either, as was shown by Shimura
1995]. (Actually he proved that no logic in the intervals SL SL + bd3 ] and
Int T2 ], save of course Int, is strongly complete.)
As far as we know, there are no examples of si-logics separating canonicity,
D-persistence and strong completeness. (Ghilardi, Meloni and Miglioli have
recently showed that SL in any language with nitely many variables is
canonical). Theorem 1.40 which holds in the intuitionistic case as well gives
an algebraic counterpart of strong Kripke completeness.

The nite model property The rst example of an innitely axiomatizable si-logic without FMP was constructed by Jankov 1968b]|that was in
fact the starting point of a long series of \negative" results in modal logic.
A nitely axiomatizable logic without FMP appeared two years later in
Kuznetsov and Gerchiu 1970]. The reader can get some impression about

126

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

this and other examples of that sort by proving (it is really not hard) that


12 6
12 6


IBM ;
@

I
@

BMB;
;
@
' =  (  ) 2= L = Int + bw4 +  ( @B;  ff1 2gg)

but no nite frame can separate ' from L. (Notice by the way that  L
is axiomatizable by Sahlqvist formulas see Chagrov and Zakharyaschev
1995b].)
FMP of a good many si-logics was proved using various forms of ltration
see e.g. Gabbay 1970], Ono 1972], Smorynski 1973], Ferrari and Miglioli
1993]. As an illustration of a rather sophisticated selective ltration we
present here the following
THEOREM 3.19 (Gabbay and de Jongh 1974) The logic Tn (see Table 5)
is characterized by the class of nite n-ary trees.

Proof First we prove that Tn is characterized by the class of nite frames
of branching  n. Suppose ' 62 Tn and M = hF Vi is a model for Tn
refuting '. Without loss of generality we may assume that F = hW Ri is a
tree. Let # = Sub' and ;x = f 2 # : x j= g, for every point x in F.

Given x in F, put rg(x) = fy] : y 2 x"g and say that x is of minimal range
if rg(x) = rg(y) for every y 2 x] \ x". Since there are only nitely many
distinct #-equivalence classes in M, every y 2 x] sees a point z 2 x] of
minimal range. Now we extract from M a nite refutation frame G = hV S i
for ' of branching  n. To begin with, we select some point x of minimal
range at which ' is refuted and put V0 = fxg.
Suppose Vk has already been dened. If jrg(x)j = 1 for every x 2 Vk , then
we put G = hV S i, where V = ki=0 Vk and S is the restriction of R to V .
Otherwise, for each x 2 Vk with jrg(x)j > 1 and each y] 2 rg(x) di erent
from x] and such that ;z  ;y for no z ] 2 rg(x) ; fx]g, we select a point
u 2 y] \ x" of minimal range. Let Ux be the set of all selected points for x
and Vk+1 = x Ux. It should be clear that ;x  ;u (and rg(x) ( rg(u)), for
every u 2 Ux , and so the inductive process must terminate. Consequently
G 6j= '.
It remains to establish that G j= Tn , i.e., G is of branching  n. Suppose
otherwise. Then there is a point x in G with m n +1 immediate successors
x0  : : :  xm , which are evidently in Ux because F is a tree. We are going to
construct a substitution instance of Tn 's axiom bbn which is refuted at x
in M.
Denote by i the conjunction of the formulas in ;xi . Since all of them
are true at xi in M, we have xi j= i  and since ;i ;j for no distinct i and

S

S

ADVANCED MODAL LOGIC

127

j , we have xj 6j= i if i 6= j . Put i = i , for 0  i < n, n = n _ : : : _ m
and consider the truth-value of the formula  = bbn f0 =p0 : : :  n =pn g at
x in M.
W
Since
xRx
for every
i
= 0 : :W
:

m
, we have x 6j= ni=0 i . Suppose
i
W that
V
W
x 6j= W ni=0 ((i ! i=6 j j ) ! i6=j j ). Then y j= i ! i6=j j and
y 6j= i6=j j , for some yW2 x" and some i 2 f0 : : : ng, and hence y 6j= i .
Since xi j= i and xi 6j= i6=j j , y sees no point in xi ] and so y 6 x (for
otherwise x would not be of minimal range). Therefore, ;xj ;y for some
j 2 f0 : : : mg, and then y j= j if j < n and y j= n if j n, which is a

V

W

W

contradiction.
It follows that x j= ni=0 ((i ! i6=j j ) ! i6=j j ), from which x 6j= ,
contrary to M being a model for bbn . It remains to notice that every nite
frame of branching  n is a reduct of a nite n-ary tree, which clearly
validates Tn .
2
Another way of obtaining general results on FMP of si-logics is to translate the corresponding results in modal logic with the help of the Preservation Theorem.
THEOREM 3.20 Every si-logic of nite depth (i.e., every logic in ExtBDn ,
for n < !) is locally tabular.
Note, however, that unlike NExtK4, the converse does not hold: the
Dummett logic LC, characterized by the class of nite chains (or by the
innite ascending chain), is locally tabular. As we saw in Section 1.7, every
non-locally tabular in NExtS4 logic is contained in Grz.3, the only prelocally tabular logic in NExtS4. But in ExtInt this way of determining
local tabularity does not work:
THEOREM 3.21 (Mardaev 1984) There is a continuum of pre-locally tabular logics in ExtInt.
Besides, it is not clear whether every locally tabular logic in ExtInt (or
NExtK4) is contained in a pre-locally tabular one.
An intuitionistic formula is said to be essentially negative if every occurrence of a variable in it is in the scope of some :. If ' is essentially negative
then T (') is a 23-formula, which yields
THEOREM 3.22 (McKay 1971, Rybakov 1978) If a si-logic L is decidable
(or has FMP) and ' is an essentially negative formula then L+' is decidable
(has FMP).
Originally this result was proved with the help of Glivenko's Theorem
(see Section 7 in Intuitionistic Logic). Say that an occurrence of a variable

128

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

in a formula is essential if it is not in the scope of any :. A formula
' is mild if every two essential occurrences of the same variable in ' are
either both positive or both negative. Kuznetsov 1972] claimed (we have
not seen the proof) that all si-logics whose extra axioms do not contain
negative occurrences of essential variables have FMP. And Wronski 1989]
announced that if L is a decidable si-logic and ' a mild formula then L + '
is also decidable.
Subframe and conal subframe si-logics|that is logics axiomatizable by
canonical formulas of the form  (F) and  (F ?), respectively|can be characterized both syntactically and semantically (see Zakharyaschev 1996]).
THEOREM 3.23 The following conditions are equivalent for every si-logic
L:
(i) L is a (conal) subframe logic
(ii) L is axiomatizable by implicative (respectively, disjunction free) formulas
(iii) L is characterized by a class of nite frames closed under the formation of (conal) subframes.
That all si-logics with disjunction free axioms have FMP was rst proved
by McKay 1968] with the help of Diego's 1966] Theorem according to which
there are only nitely many pairwise non-equivalent in Int disjunction free
formulas in variables p1  : : :  pn (see also Urquhart 1974]).
Since frames for Int contain no clusters, Theorem 1.58 and its analog
for conal subframe logics reduce in the intuitionistic case to the following
result which is due to Chagrova 1986], Rodenburg 1986], Shimura 1993]
and Zakharyaschev 1996].
THEOREM 3.24 All si-logics with disjunction free axioms are elementary
(denable by 89-sentences) and D-persistent.
Theorem 1.68 is translated into the intuitionistic case simply by replacing

K4 with Int,  with + and  with . As a consequence we obtain, for
instance, that Ono's 1972] Bn and all other logics whose canonical axioms
are built on trees have FMP. Moreover, we also have

THEOREM 3.25 (Sobolev 1977b, Nishimura 1960) All si-logics with extra
axioms in one variable have FMP and are decidable.
In fact Sobolev 1977b] proved a more general (but rather complicated)
syntactical sucient condition of FMP and constructed a formula in two
variables axiomatizing a si-logic without FMP (Shehtman's 1977] incomplete si-logic has also axioms in two variables).

ADVANCED MODAL LOGIC

129

Tabularity By the Blok{Esakia and Preservation Theorems, the situation
with tabular logics in ExtInt is the same as in NExtGrz. In particular,
L 2 ExtInt is tabular i BDn + BWn L for some n < ! i L is not a
sublogic of one of the three pretabular logics in ExtInt, namely LC, BD2
and KC + bd3 . (The pretabular si-logics were described by Maksimova
1972].) The tabularity problem is decidable in ExtInt.
3.5 Disjunction property

One of the aims of studying extensions of Int, which may be of interest
for applications in computer science, is to describe the class of constructive
si-logics. At the propositional level a logic L 2 ExtInt is regarded to be
constructive if it has the disjunction property (DP, for short) which means
that for all formulas ' and ,
' _  2 L implies ' 2 L or  2 L.
That intuitionistic logic itself is constructive in this sense was proved in a
syntactic way by Gentzen 1934{1935]. However, L( ukasiewicz (1952) conjectured that no proper consistent extension of Int has DP.
A similar property was introduced for modal logics (see e.g. Lemmon
and Scott 1977]): L 2 NExtK has the (modal) disjunction property if, for
every n 1 and all formulas '1  : : :  'n ,
2'1 _ : : : _ 2'n 2 L implies 'i 2 L, for some i 2 f1 : : :  ng:
The following theorem (in a somewhat di erent form it was proved in
Hughes and Cresswell 1984] and Maksimova 1986]) provides a semantic
criterion of DP.
THEOREM 3.26 Suppose a modal or si-logic L is characterized by a class C
of descriptive rooted frames closed under the formation of rooted generated
subframes. Then L has DP i, for every n 1 and all F1  : : :  Fn 2 C with
roots x1  : : :  xn , there is a frame F for L with root x such that the disjoint
union F1 + : : : + Fn is a generated subframe of F with fx1  : : :  xn g x".
Proof We consider only the modal case. ()) Let FL = hWL RL PLi be
a universal frame for L, big enough to contain F1 + : : : + Fn as its generated
subframe. Assuming that FL is associated with a suitable canonical model
for L, we show that there is a point x in FL such that x" = WL . The set
0 = f:2' : 9y 2 W y 6j= 'g
L
is L-consistent (for otherwise 2'1 _ : : : _ 2'n 2 L for some '1  : : :  'n 62 L).
Let be a maximal L-consistent extension of 0 and x the point in FL
where is true. Then xRL y, for every y 2 WL .

130

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

(() Suppose otherwise. Then there are formulas '1  : : :  'n 62 L such
that 2'1 _ : : : _ 2'n 2 L. Take frames F1  : : :  Fn 2 C refuting '1  : : :  'n
at their roots, respectively, and let F be a rooted frame for L containing
F1 + : : : + Fn as a generated subframe and such that its root x sees the roots
of F1  : : :  Fn . Then all the formulas 2'1  : : :  2'n are refuted at x and so
2'1 _ : : : _ 2'n 62 L, which is a contradiction.
2
It should be clear that if we use only the sucient condition of Theorem 3.26, the requirement that frames in C are descriptive is redundant.
Furthermore, it is easy to see that for L 2 NExtK4 we may assume n  2.
And clearly a logic L 2 NExtS4 has DP i , for all ' and , 2' _ 2 2 L
implies 2' 2 L or 2 2 L.
As a direct consequence of the proof above we obtain
COROLLARY 3.27 A modal or si-logic L has DP i the canonical frame
FL = hWL  RLi contains a point x such that x" = WL .
Using the semantic criterion above it is not hard to show that DP is
preserved under ,  and . It is also a good tool for proving and disproving
DP of logics with transparent semantics.
EXAMPLE 3.28 (i) Let F1  : : :  Fn be serial rooted Kripke frames. Then
the frame obtained by adding a root to F1 + : : : + Fn is also serial. Therefore,
D has DP. In the same way one can show that K, K4, T, S4, Grz, GL
and many other modal logics have DP.
(ii) Since no rooted symmetrical frame can contain a proper generated
subframe, no consistent logic in NExtKB has DP.
The rst proper extensions of Int with DP were constructed by Kreisel
and Putnam 1957]: these were KP (now called the Kreisel{Putnam logic
and SL (known as the Scott logic). We present here Gabbay's 1970] proof
that KP has DP.
THEOREM 3.29 (Kreisel and Putnam 1957) KP has DP.

Proof Using ltration one can show that KP is characterized by the class
of nite rooted frames F = hW Ri satisfying the condition

8x y z (xRy ^ xRz ^ :yRz ^ :zRy ! 9u (xRu ^ uRy ^ uRz ^
8v (uRv ! 9w (vRw ^ (yRw _ zRw))))):
(15)

If F is such a frame then for each non-empty X W 1 , the generated
subframe of F based on the set W ; (W 1 ; X )# is rooted we denote its
root by r(X ).

ADVANCED MODAL LOGIC

131

Let F1 = hW1  R1 i and F2 = hW2  R2 i be nite rooted frames satisfying
(15). We construct from them a frame F = hW Ri by taking

W = W1  W2  U
where U = fX1  X2 : X1 W11  X2 W21  X1  X2 6= g, and
xRy i (x y 2 Wi ^ xRi y) _ (x y 2 U ^ x  y) _
(x = X1  X2 2 U ^ y 2 Wi ^ r(Xi )Ri y):
It follows from the given denition that F1 + F2 is a generated subframe of
F, W1  W2 is a cover for F and W11  W21 is its root. So our theorem

will be proved if we show that (15) holds.
Suppose x y z 2 W satisfy the premise of (15). Since (15) holds for F1
and F2 , we can assume that x = X1  X2 2 U . Let Y1  Y2 and Z1  Z2 be
the sets of nal points in y" and z", respectively, with Yi  Zi Wi . By the
denition of R, we have Yi  Zi Xi . Consider u = (Y1  Z1 )  (Y2  Z2 ).
Clearly, xRu, uRy and uRz . Suppose now that v 2 u". Let w be any nal
point in v ". Then v 2 (Y1  Z1 )  (Y2  Z2 ) and so either yRw or zRw.

2

Other examples of constructive si-logics were constructed by Ono 1972]
and Gabbay and de Jongh 1974], namely, Bn and Tn . Anderson 1972]
proved that among the consistent si-logics with extra axioms in one variable
only those of the form Int + nf 2n+2 , for n 5, have DP (for n = 6 the
proof was found by Wronski 1974] see also Sasaki 1992]). Finally, Wronski
1973] showed that there is a continuum of si-logics with DP.
The additional axioms of logics in all these examples contained occurrences of _ on the other hand, known examples of si-logics with disjunction
free extra axioms, say LC, KC, Cl, BWn or BDn , were not constructive.
This observation led Hosoi and Ono 1973] to the conjecture that the disjunction free fragment of every consistent si-logic with DP coincides with
that of Int. We present a proof of this conjecture following Zakharyaschev
1987].
First we describe the conal subframe logics in NExtS4 with DP, assuming that every such logic L is represented by its independent canonical
axiomatization
L = S4  f(Fi  ?) : i 2 I g:
(16)
All frames in the rest of this section are assumed to be quasi-ordered.
Say that a nite rooted frame F with 2 points is simple if its root cluster
and at least one of the nal clusters are simple. Suppose F = hW Ri is a
simple frame, a0  a1  : : :  am am+1  : : :  an are all its points, with a0 being
the root, C (a1 ) : : :  C (am ) all the distinct immediate cluster-successors of

132

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

a0 , and an a nal point with simple C (an ). For every k = 1 : : :  n, dene a
formula k by taking
k =

^ 'ij ^ ^n 'i ^ ' ! pk

ai Raj i6=0

i=1

0
?

V

where 'ij , 'i were dened in Section 3.2 and '0? = 2( ni=1 2pi ! ?).
Now we associate with F the formula  (F) = 2p0 _ 21 if m = 1, and the
formula  (F) = 21 _ : : : _ 2m if m > 1.
LEMMA 3.30 For every simple frame F,  (F) 2 S4  (F ?).

Proof It is enough to show that G 6j=  (F) implies G 6j= (F ?), for any

nite G. So suppose  (F) is refuted in a nite frame G under some valuation.
Dene a partial map f from G onto F by taking
a0
if x 6j=  (F)
if x 6j= i , 1  i  n
f (x) = ai
undened otherwise.
One can readily check that f is a subreduction of G to F. However it is not
necessarily conal. So we extend f by putting f (x) = an , for every x of
depth 1 in G such that f (x#) = fa0g. Clearly, the improved map is still a
subreduction of G to F, and '0? ensures its conality.
2

8<
:

Using the semantical properties of the canonical formulas it is a matter
of routine to prove the following
LEMMA 3.31 Suppose i 2 f1 : : :  mg and G is the subframe of F generated
by ai . Then (G ?) 2 S4  i .
We are in a position now to prove a criterion of DP for the conal subframe logics in NExtS4.
THEOREM 3.32 A consistent conal subframe logic L 2 NExtS4 has the
disjunction property i no frame Fi in its independent axiomatization (16)
is simple, for i 2 I .

Proof ()) Suppose, on the contrary, that Fi is simple, for some i 2 I .

Since the axiomatization (16) is independent, every proper generated subframe of Fi validates L. By Lemma 3.30,  (Fi ) 2 L and so either p0 2 L or
j 2 L. However, both alternatives are impossible: the former means that
L is inconsistent, while the latter, by Lemma 3.31, implies (G ?) 2 L,
where G is the subframe of Fi generated by an immediate successor of Fi 's
root.

ADVANCED MODAL LOGIC

133

A

G  AA G2 
A 1
A 
A 
A
 y A
I
@

6 ;
@
;
@;

x

Figure 15.
(() Given two nite rooted frames G1 and G2 for L, we construct the
frame F as shown in Fig. 15 and prove that F j= L. Suppose otherwise, i.e.,
there exists a conal subreduction f of F to Fi , for some i 2 I . Let xi be the
root of Fi . Since G1 and G2 are not conally subreducible to Fi and since
L is consistent, f ;1 (xi ) = fxg. By the conality condition, it follows in
particular that y 2 domf . But then Fi is simple, which is a contradiction.
2
Thus, by Theorem 3.26, L has DP.
Note that in fact the proof of ()) shows that if L 2 NExtS4, F is
a simple frame, (F ?) 2 L and (G ?) 62 L for any proper generated
subframe G of F then L does not have DP. Transferring this observation to
the intuitionistic case, we obtain
THEOREM 3.33 (Minari 1986, Zakharyaschev 1987) If a si-logic is consistent and has DP then the disjunction free fragments of L and Int are the
same.
Sucient conditions of DP in terms of canonical formulas can be found
in Chagrov and Zakharyaschev 1993, 1997].
Since classical logic is not constructive, it is of interest to nd maximal
consistent si-logics with DP. That they exist follows from Zorn's Lemma.
Here is a concrete example of such a logic.
Trying to formalize the proof interpretation of intuitionistic logic, Medvedev (1962) proposed to treat intuitionistic formulas as nite problems.
Formally, a nite problem is a pair hX Y i of nite sets such that Y X
and X 6=  elements in X are called possible solutions and elements in Y
solutions to the problem. The operations on nite problems, corresponding
to the logical connectives, are dened as follows:
hX1  Y1 i ^ hX2  Y2 i = hX1 ' X2  Y1 ' Y2 i 
hX1  Y1 i _ hX2  Y2 i = hX1 t X2  Y1 t Y2 i 

134

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV






I
@
@



@;


;
;





I
@
@
;
I
6
;
6
@;
@;
; @; @

;
I
@
@ 6;
@;


1

1

1



6
@
6
;
I
@

;
I
6
;
I
@
;


@

;
@
;
@
 


;



;
@
;
@
@

 
1

1

1




I
@

;
I
@

;
I
@

;
6
6 @

 6;
@; @
;






;
@
;
@
@;

 
1


 
;
I
@
@ 6;


@;

Figure 16.

D

hX1  Y1 i ! hX2  Y2 i = X2X1  ff 2 X2X1 : f (Y1 )

E

Y2 g 

? = hX i :
Here X t Y = (X ' f1g)  (Y ' f2g) and X Y is the set of all functions from
X into Y . Note that in the denition of ? the set X is xed, but arbitrary
for deniteness one can take X = fg.
Now we can interpret formulas by nite problems. Namely, given a formula ', we replace its variables by arbitrary nite problems and perform
the operations corresponding to the connectives in '. If the result is a
problem with a non-empty set of solutions no matter what nite problems
are substituted for the variables in ', then ' is called nitely valid. One
can show that the set of all nitely valid formulas is a si-logic it is called
Medvedev's logic and denoted by ML.
In fact, ML can be dened semantically. Medvedev (1966) showed that
ML coincides with the set of formulas that are valid in all frames Bn having
the form of the n-ary Boolean cubes with the topmost point deleted for
n = 1 2 3 4, the Medvedev frames are shown in Fig. 16. Since Bn + Bm is
a generated subframe of Bn+m , ML has DP. Moreover, Levin 1969] proved
that it has no proper consistent extension with DP. The following proof of
this result is due to Maksimova 1986].

THEOREM 3.34 (Levin 1969) ML is a maximal si-logic with DP.

Proof Suppose, on the contrary, that there exists a proper consistent extension L of ML having DP. Then we have a formula ' 2 L ; ML. We
show rst that there is an essentially negative substitution instance ' of
' such that ' 62 ML. Since '(p1  : : :  pn ) 62 ML, there is a Medvedev

frame Bm refuting ' under some valuation V. With every point x in Bm
we associate a new variable qx and extend V to these variables by taking
V(qx ) to be the set of nal points in Bm that are not accessible from x. By

ADVANCED MODAL LOGIC

135

the construction of Bm , we have y j= :qx i y 2 x", from which

V(

_ :qx) = V(pi):

x2V(pi )

W
W
Let ' = '( x V p :qx  : : :  x V p :qx ). It follows that V(' ) = V(')
2 ( 1)

2 ( n)

and so ' 62 ML.
Thus, we may assume that ' is an essentially negative formula. Since
KP ML, ML contains the formulas

ndk = (:p ! :q1 _ : : : _ :qk ) ! (:p ! :q1) _ : : : _ (:p ! :qk )

which, as is easy to see, belong to KP. Let us consider the logic

ND = Int + fndk : k 1g:

Using the fact that the outermost ! in ndk can be replaced with $ and that
(:p ! :q) $ :(:p ^ q) 2 Int, one can readily show that every essentially
negative formula is equivalent in ND to the conjunction of formulas of the
form :1 _: : :_:l . So L;ML contains a formula of the form :1 _: : :_:l .
Since L has DP, :i 2 L for some i. But then, by Glivenko's Theorem,
:i 2 ML, which is a contradiction.
2

Remark. ML is not nitely axiomatizable, as was shown by Maksimova

et al. 1979]. Nobody knows whether it is decidable.
It turns out, however, that ML is not the unique maximal logic with DP
in ExtInt. Kirk 1982] noted that there is no greatest consistent si-logic
with DP. Maksimova 1984] showed that there are innitely many maximal
constructive si-logics, and Chagrov 1992a] proved that in fact there are
a continuum of them see also Ferrari and Miglioli 1993, 1995a, 1995b].
Galanter 1990] claims that each si-logic characterized by the class of frames
of the form
hfW : W

f1 : : :  ng W 6=  jW j 62 N g i 

where n = 1 2 : : : and N is some xed innite set of natural numbers, is a
maximal si-logic with DP.

3.6 Intuitionistic Modal Logics

All modal logics we have dealt with so far were constructed on the classical
non-modal basis. It can be replaced by logics of other types. For instance,
one can consider modal logics based on relevant logic (see e.g. Fuhrmann
1989]) or many-valued logics (see e.g. Segerberg 1967], Morikawa 1989],

136

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Ostermann 1988]), and many others. In this section we briey discuss
modal logics with the intuitionistic basis.
Unlike the classical case, the intuitionistic 2 and 3 are not supposed to
be dual, which provides more possibilities for dening intuitionistic modal
logics. For a non-empty set M of modal operators, let LM be the standard propositional language augmented by the connectives in M. By an
intuitionistic modal logic in the language LM we understand any subset of
LM containing Int and closed under modus ponens, substitution and the
regularity rule ' ! = # ' ! #, for every # 2 M.
There are three ways of dening intuitionistic analogues of (classical)
normal modal logics. First, one can take the family of logics extending the
basic system IntK2 in the language L2 which is axiomatized by adding to
Int the standard axioms of K

2(p ^ q) $ 2p ^ 2q and 2>:
An example of a logic in this family is Kuznetsov's 1985] intuitionistic
provability logic I4 (Kuznetsov used 4 instead of 2), the intuitionistic
analog of the provability logic GL. It can be obtained by adding to IntK2
(and even to Int) the axioms

p ! 2p (2p ! p) ! p ((p ! q) ! p) ! (2q ! p):
A model theory for logics in NExtIntK2 was developed by Ono 1977],
Bo)zic and Do)sen 1984], Do)sen 1985a], Sotirov 1984] and Wolter and Zakharyaschev 1997a,b] we discuss it below. Font 1984, 1986] considered
these logics from the algebraic point of view, and Luppi 1996] investigated
their interpolation property by proving, in particular, that the superamalgamability of the corresponding varieties of algebras is equivalent to interpolation.
A possibility operator 3 in logics of this sort can be dened in the classical
way by taking 3' = :2:'. Note, however, that in general this 3 does not
distribute over disjunction and that the connection via negation between 2
and 3 is too strong from the intuitionistic standpoint (actually, the situation
here is similar to that in intuitionistic predicate logic where 9 and 8 are not
dual.)
Another family of \normal" intuitionistic modal logics can be dened in
the language L3 by taking as the basic system the smallest logic in L3 to
contain the axioms

3(p _ q) $ 3p _ 3q and :3?
it will be denoted by IntK3 . Logics in NExtIntK3 were studied by Bo)zic
and Do)sen 1984], Do)sen 1985a], Sotirov 1984] and Wolter 1997c].

ADVANCED MODAL LOGIC

137

Finally, we can dene intuitionistic modal logics with independent 2 and
3. These are extensions of IntK23 , the smallest logic in the language L23

containing both IntK2 and IntK3 . Fischer Servi 1980, 1984] constructed a
logic in NExtIntK23 by imposing a weak connection between the necessity
and possibility operators:

FS = IntK23  3(p ! q) ! (2p ! 3q)  (3p ! 2q) ! 2(p ! q):
A remarkable feature of FS is that the standard translation ST of modal
formulas into rst order ones (see Correspondence Theory) not only embeds
K into classical predicate logic but also FS into intuitionistic rst order

logic: ' belongs to the former i ST (') is a theorem of the latter. According
to Simpson 1994], this result was proved by C. Stirling see also Grefe 1997].
Various extensions of FS were studied by Bull 1966a], Ono 1977], Fischer
Servi 1977, 1980, 1984], Amati and Pirri 1994], Ewald 1986], Wolter and
Zakharyaschev 1997b], Wolter 1997c]. The best known one is probably the
logic

MIPC = FS  2p ! p  2p ! 22p  3p ! 23p 
p ! 3p  33p ! 3p  32p ! 2p

introduced by Prior 1957]. Bull 1966a] noticed that the translation dened by
(pi ) = Pi (x), ? = ?,
( $ ) =  $  , for $ 2 f^ _ !g,
(2) = 8x  , (3) = 9x 
is an embedding of MIPC into the monadic fragment of intuitionistic predicate logic. Ono 1977], Ono and Suzuki 1988], Suzuki 1990], and Bezhanishvili 1997] investigated the relations between logics in NExtMIPC and
superintuitionistic predicate logics induced by that translation.
In what follows we restrict attention only to the classes of intuitionistic
modal logics introduced above. An interesting example of a system not
covered here was constructed by Wijesekera 1990]. A general model theory
for such logics is developed by Sotirov 1984] and Wolter and Zakharyaschev
1997b].
Let us consider rst the algebraic and relational semantics for the logics
introduced above. All the semantical concepts to be dened below turn
out to be natural combinations of the corresponding notions developed for
classical modal and si-logics. For details and proofs we refer the reader to
Wolter and Zakharyaschev 1997a,b].
From the algebraic point of view, every logic L 2 NExtIntKM , for M
f2 3g, corresponds to the variety of Heyting algebras with one or two

138

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

operators validating L. The variety of algebras for IntKM will be called the
variety of M-algebras.
To construct the relational representations of M-algebras, we dene a 2frame to be a structure of the form hW R R2  P i in which hW R P i is an
intuitionistic frame, R2 a binary relation on W such that

R  R2  R = R2
and P is closed under the operation

2X = fx 2 W : 8y 2 W (xR2 y ! y 2 X )g:
A 3-frame has the form hW R R3  P i, where hW R P i is again an intuitionistic frame, R3 a binary relation on W satisfying the condition
R;1  R3  R;1 = R3
and P is closed under
3X = fx 2 W : 9y 2 X xR3 yg:
Finally, a 23-frame is a structure hW R R2 R3  P i the unimodal reducts
hW R R2  P i and hW R R3  P i of which are 2- and 3-frames, respec-

tively. (To see why the intuitionistic and modal accessibility relations are
connected by the conditions above the reader can construct in the standard
way the canonical models for the logics under consideration. The important
point here is that we take the Leibnizean denition of the truth-relation for
the modal operators. Other denitions may impose di erent connecting
conditions see below.)
Given a 23-frame F = hW R R2 R3  P i, it is easy to check that its dual

F+ = hP \  !  2 3i
is a 23-algebra. Conversely, for each 23-algebra A = hA ^ _ ! ? 2 3i
we can dene the dual frame

A+ = hW R R2 R3  P i
by taking hW R P i to be the dual of the Heyting algebra hA ^ _ ! ?i
and putting
r1 R2 r2 i 8a 2 A (2a 2 r1 ! a 2 r2 )
r1 R3 r2 i 8a 2 A (a 2 r2 ! 3a 2 r1 ):
A+ is a 23-frame and, moreover, A 
= (A+ )+ . Using the standard technique
of the model theory for classical modal and si-logics, one can show that a

ADVANCED MODAL LOGIC

139

23-frame F is isomorphic to its bidual (F+ )+ i F = hW R R2 R3  P i is
descriptive, i.e., hW R P i is a descriptive intuitionistic frame and, for all
x y 2 W ,
xR2 y i 8X 2 P (x 2 2X ! y 2 X )
xR3 y i 8X 2 P (y 2 X ! x 2 3X ):
Thus we get the following completeness theorem.

THEOREM 3.35 Every logic L 2 NExtIntK23 is characterized by a suitable class of (descriptive) 23-frames, e.g. by the class fA+ : A j= Lg.
Similar results hold for logics in NExtIntK2 and NExtIntK3 .
As usual, by a Kripke frame we understand a frame hW R R2  R3  P i
in which P consists of all R-cones in this case we omit P . An intuitionistic modal logic L is D-persistent if the underlying Kripke frame of each
descriptive frame for L validates L. For example, FS as well as the logics

L(k l m n) = IntK23  3k 2l p ! 2m 3np for k l m n 0
are D-persistent and so Kripke complete (see Wolter and Zakharyaschev
1997b]). Descriptive frames validating FS satisfy the conditions

xR3 y ! 9z (yRz ^ xR2 z ^ xR3 z )
xR2 y ! 9z (xRz ^ zR2y ^ zR3y)
and those for L(k l m n) satisfy
xR3k y ^ xR2m y ! 9u (yR2l u ^ zR3n u):

It follows, in particular, that MIPC is D-persistent its Kripke frames have
the properties: R2 is a quasi-order, R3 = R2;1 and R2 = R  (R2 \ R3 ). On
the contrary, I4 is not D-persistent, although it is complete with respect to
the class of Kripke frames hW R R2i such that hW R2 i is a frame for GL
and R the reexive closure of R2 .
The next step in constructing duality theory of M-algebras and M-frames
is to nd relational counterparts of the algebraic operations of forming homomorphisms, subalgebras and direct products. Let F = hW R R2  R3  P i
be a 23-frame and V a non-empty subset of W such that
8x 2 V 8y 2 W (xR2 y _ xRy ! y 2 V )

8x 2 V 8y 2 W (xR3 y ! 9z 2 V (xR3 z ^ yRz )):
Then G = hV R V R2 V R3 V fX \ V : X 2 P gi is also a 23-frame
which is called the subframe of F generated by V . The former of the two

140

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

z

y R -z
K
A






R3A R3

F Ax

6

R3

G x

Figure 17.
0


1 R3 4



R

R3A R

K
A

6


2

F

01 S3 4



I S3; 6
@
S 6;
@
S S




3

A

; S @
G 2 33

3

Figure 18.
conditions above is standard: it requires V to be upward closed with respect
to both R and R2. However, the latter one does not imply that V is upward
closed with respect to R3 : the frame G in Fig. 17 is a generated subframe
of F, although the set fx z g is not an R3 -cone in F. This is one di erence
from the standard (classical modal or intuitionistic) case. Another one arises
when we dene the relational analog of subalgebras.
Given 23-frames F = hW R R2  R3  P i and G = hV S S2  S3  Qi, we
say a map f from W onto V is a reduction of F to G if f ;1 (X ) 2 P for
every X 2 Q and, for all x y 2 W and u 2 V ,
xRy implies f (x)Sf (y),
xR y implies f (x)S f (y), for # 2 f2 3g,
f (x)Su implies 9z 2 f ;1(u) xRz ,
f (x)S2 u implies 9z 2 f ;1(u) xR2 z ,
f (x)S3 u implies 9z 2 W (xR3 z ^ uSf (z )),
Again, the last condition di ers from the standard one: given f (x)S3 f (y),
in general we do not have a point z such that xR3 z and f (y) = f (z ), witness
the map gluing 0 and 1 in the frame F in Fig. 18 and reducing it to G.
Note that both these concepts coincide with the standard ones in classical
modal frames, where R and S are the diagonals. The relational counterpart
of direct products|disjoint unions of frames|is dened as usual.
THEOREM 3.36 (i) If G is the subframe of a 23-frame F generated by V
then the map h dened by h(X ) = X \ V , for X an element in F+, is a

ADVANCED MODAL LOGIC

141

homomorphism from F+ onto G+ .
(ii) If h is a homomorphism from a 23-algebra A onto a 23-algebra B
then the map h+ dened by h+ (r) = h;1 (r), r a prime lter in B, is an
isomorphism from B+ onto a generated subframe of A+ .
(iii) If f is a reduction of a 23-frame F to a 23-frame G then the map
f + dened by f +(X ) = f ;1(X ), X an element in G+ , is an embedding of
G+ into F+ .
(iv) If B is a subalgebra of a 23-algebra A then the map f dened by
f (r) = r\ B , r a prime lter in A and B the universe of B, is a reduction
of A+ to B+ .

This duality can be used for proving various results on modal denability.
For instance, a class C of 23-frames is of the form C = fF : F j= ;g, for some
set ; of L23 -formulas, i C is closed under the formation of generated subframes, reducts, disjoint unions, and both C and its complement are closed
under the operation F 7! (F+ )+ (see Wolter and Zakharyaschev 1997b]).
Moreover, one can extend Fine's Theorem connecting the rst order denability and D-persistence of classical modal logics to the intuitionistic modal
case:
THEOREM 3.37 If a logic L 2 NExtIntK23 is characterized by an elementary class of Kripke frames then L is D-persistent.
These results may be regarded as a justication for the relational semantics introduced in this section. However, it is not the only possible one. For
example, Bo)zic and Do)sen 1984] impose a weaker condition on the connection between R and R2 in 2-frames. Fisher Servi 1980] interprets FS
in birelational Kripke frames of the form hW R S i in which R is a partial
order, R  S S  R, and

xRy ^ xSz ! 9u (ySu ^ zRu):
The intuitionistic connectives are interpreted by R and the truth-conditions
for 2 and 3 are dened as follows
2X = fx 2 W : 8y z (xRySz ! z 2 X g
3X = fx 2 W : 9y 2 X xSyg:
In birelational frames for MIPC S is an equivalence relation and
xSyRz ! 9u xRuSz:
These frames were independently introduced by L. Esakia who also established duality between them and \monadic Heyting algebras".

142

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

There are two ways of investigating various properties of intuitionistic
modal logics. One is to continue extending the classical methods to logics
in NExtIntKM . Another one uses those methods indirectly via embeddings
of intuitionistic modal logics into classical ones. That such embeddings
are possible was noticed by Shehtman 1979], Fischer Servi 1980, 1984],
and Sotirov 1984]. Our exposition here follows Wolter and Zakharyaschev
1997a,b]. For simplicity we conne ourselves only to considering the class
NExtIntK2 and refer the reader to the cited papers for information about
more general embeddings.
Let T be the translation of L2 into L2I 2 prexing 2I to every subformula of a given L2 -formula. Thus, we are trying to embed intuitionistic
modal logics in NExtIntK2 into classical bimodal logics with the necessity
operators 2I (of S4) and 2. Say that T embeds L 2 NExtIntK2 into
M 2 NExt(S4 & K) (S4 in L2I and K in L2 ) if, for every ' 2 L2 ,

' 2 L i T (') 2 M:
In this case M is called a bimodal (or BM-) companion of L.
For every logic M 2 NExt(S4 & K) put

M = f' 2 L2 : T (') 2 M g

and let  be the map from NExtIntK2 into NExt(S4 & K) dened by

(IntK2  ;) = (Grz & K)  mix  T (;)
where ; L2 and mix = 2I 22I p $ 2p. (The axiom mix reects the

condition R  R2  R = R2 of 2-frames.) Then we have the following
extension of the embedding results of Maksimova and Rybakov 1974], Blok
1976] and Esakia 1979a,b]:
THEOREM 3.38 (i) The map  is a lattice homomorphism from the lattice
NExt(S4 & K) onto NExtIntK2 preserving decidability, Kripke completeness, tabularity and the nite model property.
(ii) Each logic IntK2  ; is embedded by T into any logic M in the
interval
(S4 & K)  T (;) M

(Grz & K)  mix  T (;):

(iii) The map  is an isomorphism from the lattice NExtIntK2 onto the
lattice NExt(Grz & K)  mix preserving FMP and tabularity.
Note that Fischer Servi 1980] used another generalization of the Godel
translation. She dened
T (3') = 3T (')

ADVANCED MODAL LOGIC

143

T (2') = 2I 2T (')

and showed that this translation embeds FS into the logic

(S4 & K)  32I p ! 2I 3p  33I p ! 3I 3p:

It is not clear, however, whether all extensions of FS can be embedded into
classical bimodal logics via this translation.
Let us turn now to completeness theory of intuitionistic modal logics. As
to the standard systems I4, FS, and MIPC, their FMP can be proved
by using (sometimes rather involved) ltration arguments see Muravitskij 1981], Simpson 1994] and Grefe 1997], and Ono 1977], respectively.
Further results based on the ltration method were obtained by Sotirov
1984] and Ono 1977]. However, in contrast to classical modal logic, only a
few general completeness results covering interesting classes of intuitionistic
modal logics are known. The proofs of the following two theorems are based
on the translation into classical bimodal logics discussed above.
THEOREM 3.39 Suppose that a si-logic Int + ; has one of the properties:
decidability, Kripke completeness, FMP. Then the logics IntK2  ; and
IntK2  ;  2p ! p also have the same property.

Proof It suces to show that there is a BM-companion of each of these
systems satisfying the corresponding property. Notice that

((S4  T (;)) & K) = IntK2  ;

((S4  T (;)) & (K  2p ! p)) = IntK2  ;  2p ! p:

So it remains to use the fact that if Int + ; has one of the properties
under consideration then its smallest modal companion S4  T (;) has this
property as well (Table 7), and if L1 , L2 are unimodal logics having one
of those properties then the fusion L1 & L2 also enjoys the same property
(Theorem 2.6).
2
Such a simple reduction to known results in classical modal logic is not
available for logics containing IntK42 = IntK2  2p ! 22p. However,
by extending Fine's 1974] method of maximal points to bimodal companions of extensions of IntK42 Wolter and Zakharyaschev 1997a] proved the
following:
THEOREM 3.40 Suppose L  IntK42 has a D-persistent BM-companion
M  (S4 & K4)  mix whose Kripke frames are closed under the formation
of substructures. Then
(i) for every set ; of intuitionistic negation and disjunction free formulas,
L  ; has FMP

144

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

(ii) for every set ; of intuitionistic disjunction free formulas and every

n 1,

L;

_n (pi ! _ pj )

i=0

j 6=i

has the nite model property.
One can use this result to show that the following (and many other)
intuitionistic modal logics enjoy FMP:
(1) IntK42
(2) IntS42 = IntK42  2p ! p (R2 is reexive)
(3) IntS4:32 = IntS42  2(2p ! q) _ 2(2q ! p) (R2 is reexive and
connected)
(4) IntK42  p _ 2:2p (R2 is symmetrical)
(5) IntK42  2p _ 2:2p (R2 is Euclidean)
(6) IntK42  2p _ :2p (xRy ^ xR2 z ! yR2z )
We conclude this section with some remarks on lattices of intuitionistic modal logics. Wolter 1997c] uses duality theory to study splittings of
lattices of intuitionistic modal logics. For example, he showed that each
nite rooted frame splits NExt(L  2n p ! 2n+1 p), for L = IntK2 and
L = FS, and each R2 -cycle free nite rooted frame splits the lattices of
extensions of IntK2 and FS. No positive results are known, however, for
the lattice NExtIntK3 . In fact, the behavior of 3-frames is quite di erent
from that of frames for FS. For instance, in classical modal logic we have
RGF = GRF , for each class of frames (or even 2-frames) F , where G and R
are the operations of forming generated subframes and reducts, respectively.
But this does not hold for 3-frames. More precisely, there exists a nite
3-frame G such that RGfGg 6 GRfGg. In other terms, the variety of modal
algebras for K has the congruence extension property (i.e., each congruence
of a subalgebra of a modal algebra can be extended to a congruence of the
algebra itself) but this is not the case for the variety of 3-algebras.
Vakarelov 1981, 1985] and Wolter 1997c] investigate how logics having
Int as their non-modal fragment are located in the lattices of intuitionistic
modal logics. It turns out, for instance, that in NExtIntK3 the inconsistent
logic has a continuum of immediate predecessors all of which have Int as
their non-modal fragment, but no such logic exists in the lattice of extensions
of IntK2 .

4 ALGORITHMIC PROBLEMS
All algorithmic results considered in the previous sections were positive:
we presented concrete procedures for deciding whether an arbitrary given

ADVANCED MODAL LOGIC

145

formula belongs to a given logic in some class or whether it axiomatizes
a logic with a certain property. What is the complexity of those decision
algorithms? Do there exist undecidable calculi18 and properties? These are
the main questions we address in this chapter.

4.1 Undecidable calculi

The rst undecidable modal and si-calculi were constructed by Thomason
1975c] (polymodal and unimodal), Isard 1977] (unimodal) and Shehtman
1978b] (superintuitionistic). However, we begin with the very simple example of Shehtman 1982] which is a modal reformulation of the undecidable
associative calculus T of Tseitin 1958]. The axioms of T are
ac = ca
ad = da
bc = cb
bd = db
edb = be
eca = ae
abac = abacc:
The reader will notice immediately an analogy between them and the axioms
of the following modal calculus with ve necessity operators:
L = K5  21 23 p $ 23 21 p  21 24 p $ 24 21 p 
22 23 p $ 23 22 p  22 24 p $ 24 22 p 
25 24 22 p $ 22 25 p  25 23 21 p $ 21 25 p 
21 22 21 23 p $ 21 22 21 23 23 p:
Moreover, it is not hard to see that words x, y in the alphabet fa b c d eg
are equivalent in T 19 i f (x)p $ f (y)p 2 K5 , where f is the natural
one-to-one correspondence between such words and modalities in language
f21  : : :  25 g under which, for instance, f (cadedb) = 23 21 24 25 24 22 . It
follows immediately that L is undecidable. Using the undecidable associative calculus of Matiyasevich 1967], one can construct in the same way an
undecidable bimodal calculus having three reductions of modalities as its
axioms. It is unknown whether there is an undecidable unimodal calculus
axiomatizable by reductions of modalities.
Thomason's simulation and the undecidable polymodal calculi mentioned
above provide us with examples of undecidable calculi in NExtK. However,
to nd axioms of undecidable unimodal calculi with transitive frames, as
well as undecidable si-calculi, a more sophisticated construction is required.
18 By a calculus we mean a logic with nitely many axioms (inference rules in our case
are xed).
19 I.e., they can be obtained from each other by a nite number of transformations of
the form w1 ww2 ! w1 vw2 , where w = v or v = w is an axiom of T .

146

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

b X
yXX d
X

X
yXX

a

X
yXX d1
XX
yXX d2
XX
X



yXX g1


I XX
g@
yXX g2
@a0 @
X

0 I@ 1 
I 
6
a0 @
@a2
6
0
 a01
 a11
6a21
.6a02
.6a12
.6a22
..
..
..
 a0t;1  a1k;1  a2l;1
.6a0t
.6a1k *.6a2l
..J]
..
..

J 
. . .J. . .
e(t k l)
6




Figure 19.
Instead of associative calculi, let us use now Minsky machines with two
tapes (or register machines with two registers). A Minsky machine is a
nite set (program) of instructions for transforming triples hs m ni of natural numbers, called congurations. The intended meaning of the current
conguration hs m ni is as follows: s is the number (label) of the current
machine state and m, n represent the current state of information. Each
instruction has one of the four possible forms:

s ! ht 1 0i  s ! ht 0 1i 
s ! ht ;1 0i (ht0  0 0i) s ! ht 0 ;1i (ht0  0 0i):
The last of them, for instance, means: transform hs m ni into ht m n ; 1i
if n > 0 and into ht0  m ni if n = 0. For a Minsky machine P , we shall
write P : hs m ni ! ht k li if starting with hs m ni and applying the

instructions in P , in nitely many steps (possibly, in 0 steps) we can reach
ht k li.
We shall use the well known fact (see e.g. Mal'cev 1970]) that the following conguration problem is undecidable: given a program P and congurations hs m ni, ht k li, determine whether P : hs m ni ! ht k li.
With every program P and conguration hs m ni we associate the transitive frame F depicted in Fig. 19. Its points e(t k l) represent congurations
ht k li such that P : hs m ni ! ht k li e(t k l) sees the points a0t , a1k , a2l

ADVANCED MODAL LOGIC

147

representing the components of ht k li. The following variable free formulas
characterize points in F in the sense that each of these formulas, denoted by
Greek letters with subscripts and/or superscripts, is true in F only at the
point denoted by the corresponding Roman letter with the same subscript
and/or superscript:

 = 3> ^ 23>  = 2?  = 3 ^ 3 ^ :32
= : ^ 3 ^ :32 1 = 3 ^ :32  2 = 3 1 ^ :32 1 
1 = 3 ^ :32 ^ :3  2 = 31 ^ :321 ^ :3 
00 = 3 ^ 3 ^ :32  ^ :32 
10 = 31 ^ 3 1 ^ :321 ^ :32 1 
20 = 32 ^ 3 2 ^ :322 ^ :32 2 
^
ij+1 = 3ij ^ :32ij ^ :30k 
i6=k

where i 2 f0 1 2g, j 0. The formulas characterizing e(t k l) are denoted
by (t 1k  2l ), where

(t ' ) =

^t 3 ^ :3
0

i=0

i

0
t+1

^ 3' ^ :32' ^ 3 ^ :32:

We require also formulas characterizing not only xed but arbitrary congurations:
1 = (310 _ 10 ) ^ :300 ^ :320 ^ p1 ^ :3p1
2 = 310 ^ :300 ^ :320 ^ 3p1 ^ :32 p1 
1 = (320 _ 20 ) ^ :300 ^ :310 ^ p2 ^ :3p2 
2 = 320 ^ :300 ^ :310 ^ 3p2 ^ :32p2 :
Now we are fully equipped to simulate the behavior of Minsky machines by
means of modal formulas. Let us consider for simplicity only tense logics
and observe that F satises the condition
8x8y9z (xRzR;1y _ xR;1 zRy _ xRy _ xR;1 y _ x = y):

So, for every valuation in F, a formula ' is true at some point in F i the
formula
#' = 33;1' _ 3;13' _ 3' _ 3;1' _ '
is true at all points in F, i.e., the modal operator # can be understood
as \omniscience". Let  be a formula which is refuted in F and does not

148

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

contain p1 and p2 . With each instruction I in P we associate a formula
AxI by taking:

AxI = : ^ #(t 1  1 ) ! : ^ #(t0  2  1 )
if I has the form t ! ht0  1 0i,

AxI = : ^ #(t 1  1 ) ! : ^ #(t0  1  2 )
if I is t ! ht0  0 1i,

AxI = (: ^ #(t 2  1 ) ! : ^ #(t0  1  1 )) ^
(: ^ #3(t 10 1 ) ! : ^ #(t00  10  1 ))
if I is t ! ht0  ;1 0i (ht00  0 0i),

AxI = (: ^ #(t 1  2 ) ! : ^ #(t0  1  1 )) ^
(: ^ #(t 1  20 ) ! : ^ #(t00  1  20 ))
if I is t ! ht0  0 ;1i (ht00  0 0i). The formula simulating P as a whole is

AxP =

^ AxI:

I 2P

Now, by induction on the length of computations and using the frame F in
Fig. 19 one can show that for every program P and congurations hs m ni,
ht k li, we have P : hs m ni ! ht k li i
: ^ #(s 1m  2n ) ! : ^ #(t 1k  2l ) 2 K4:t  AxP:

Thus, if the conguration problem is undecidable for P then the tense
calculus K4:t  AxP is undecidable too. In the same manner (but using
somewhat more complicated frames and formulas) one can construct undecidable calculi in NExtK4 and even ExtInt for details consult Chagrova
1991] and Chagrov and Zakharyaschev 1997]. The following table presents
some "quantitative characteristics" of known undecidable calculi in various
classes of logics. Its rst line, for instance, means that there is an undecidable si-calculus with axioms in 4 variables and the derivability problem in
it is undecidable in the class of formulas in 2 variables = means that the
number of variables is optimal, and  indicates that the optimal number is
still unknown.

ADVANCED MODAL LOGIC

149

The number of variables in
Class of logics undecidable calculi separated formulas
ExtInt
 4 2
=2
NExtS4
 3 2
=1
ExtS4
3
=1
NExtGL
=1
=1
ExtGL
=1
=1
ExtS
=1
=1
NExtK4
=1
=0
ExtK4
=1
=0
These observations follow from Anderson 1972], Chagrov 1994], Sobolev
1977b], and Zakharyaschev 1997a]. Say that a formula  is undecidable in
(N)ExtL if no algorithm can determine for an arbitrary given ' whether
 2 L + ' (respectively,  2 L  '). For example, formulas in one variable,
the axioms of BWn and BDn are decidable in ExtInt. On the other hand,
there are purely implicative undecidable formulas in ExtInt, and
:(p ^ q) _ :(:p ^ q) _ :(p ^ :q) _ :(:p ^ :q)
is the shortest known undecidable formula in this class. Here are some modal
examples: the formula 2(22 ? ! 2p _ 2:p) is undecidable in NExtGL,
2+ :2+ p _ 2+ :2+ :2+ p in ExtS, ? in ExtK4 and NExtK4:t in NExtK
and NExtK4:t undecidable is the conjunction of axioms of any consistent
tabular logic in these classes. However, no non-trivial criteria are known for
a formula to be decidable it is unclear also whether one can e ectively
recognize the decidability of formulas in the classes ExtInt, (N)ExtS4,
(N)ExtGL, ExtS, (N)ExtK4.

4.2 Admissibility and derivability of inference rules

Another interesting algorithmic problem for a logic L is to determine whether
an arbitrary given inference rule '1  : : :  'n =' is derivable in L, i.e., ' is
derivable in L from the assumptions '1  : : :  'n , and whether it is admissible in L, i.e., for every substitution s, 's 2 L whenever '1 s : : :  'n s 2 L.
(Note that derivability depends on the postulated inference rules in L,
while admissibility depends only on the set of formulas in L.) Admissible
and derivable rules are used for simplifying the construction of derivations.
Derivable rules, like the well known rule of syllogism
' !   !  
'!
may replace some fragments of xed length in derivations, thereby shortening them linearly. Admissible rules in principle may reduce derivations

150

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

more drastically. Since ' 2 L i the rule >=' is derivable (or admissible)
in L, the derivability and admissibility problems for inference rules may be
regarded as generalizations of the decidability problem.
If the only postulated rules in L are substitution and modus ponens, the
Deduction Theorem reduces the derivability problem for inference rules in
L to its decidability:

'1  : : :  'n is derivable in L i ' ^ : : : ^ ' !  2 L:
1
n

However, if the rule of necessitation '=2' is also postulated in L, we have
only
'1  : : :  'n is derivable in L i '  : : :  ' ` :
1
n L

For n-transitive L this is equivalent to 2n ('1 ^ : : : ^ 'n ) !  2 L, and so
the derivability problem for inference rules in n-transitive logics is decidable

i the logics themselves are decidable. In general, in view of the existential
quantier in Theorem 1.1, the situation is much more complicated.
Notice rst that similarly to Harrop's Theorem, a sucient condition for
the derivability problem to be decidable in a calculus is its global FMP (see
Section 1.5). Thus we have
THEOREM 4.1 The derivability problem for inference rules in K, T, D,
KB is decidable.

Moreover, sometimes we can obtain an upper bound for the parameter m
in the Deduction Theorem, which also ensures the decidability of the derivability problem for inference rules. One can prove, for instance, that for K
it is enough to take m = 2jSub' Subj . In general, however, the derivability
problem for inference rules in a logic L turns out to be more complex than
the decidability problem for L. (Recall, by the way, that there are logics
with FMP but not global FMP.)
THEOREM 4.2 (Spaan 1993) There is a decidable calculus in NExtK the
derivability problem for inference rules in which is undecidable.
Spaan proves this result by simulating in `L , L a decidable logic dened
below, the following undecidable tiling problem: given a nite set of tiles
T , can T tile N ' N ? The logic L is surprisingly simple:

L = Alt2 

^ 33pi ! _ 33(pi ^ pj ):

1i4

1i<j 4

It is a subframe logic, so it is D-persistent and has FMP (because Alt2 L
see Theorem 1.22 and Proposition 1.59). Note also that the bimodal logic

ADVANCED MODAL LOGIC

151

Lu (see Section 2.2) is a complete and elementary subframe logic which

is undecidable because `L is undecidable. Using this observation one can
construct a unimodal subframe logic in NExtK with the same properties.
Let us turn now to the admissibility problem. It is not hard to see that
the rules
(::p ! p) ! p _ :p and
:p ! q _ r
:p _ ::p
(:p ! q) _ (:p ! r)
are admissible but not derivable in Int and 3p ^ 3:p=? is admissible but
not derivable in any extension of S4.3 save those containing 23p ! 32p,
in which it is derivable. (Recall that a logic L is said to be structurally
complete if every admissible inference rule in L is derivable in L. We have
just seen that Int as well as S4.3 are not structurally complete. For more
information on structural completeness see e.g. Tsytkin 1978, 1987] and
Rybakov 1995].) The following result strengthens Fine's 1971] Theorem
according to which all logics in ExtS4.3 are decidable.
THEOREM 4.3 (Rybakov 1984a) The admissibility problem for inference
rules is decidable in every logic containing S4.3.
An impetus for investigations of admissible inference rules in various
logics was given by Friedman's 1975] problem 40 asking whether one can
e ectively recognize admissible rules in Int. This problem turned out to be
closely connected to the admissibility problem in suitable modal logics. We
demonstrate this below for the logic GL following Rybakov 1987, 1989].
First we show that dealing with logics in NExtK, it is sucient to consider
inference rules of a rather special form. Let '(q1  : : :  q2n+2 ) be a formula
containing no 2 and 3 and represented in the full disjunctive normal form.
Say that an inference rule is reduced if it has the form
'(p0  : : :  pn 3p0 : : :  3pn)=p0 :
THEOREM 4.4 For every rule '= one can eectively construct a reduced
rule '0 =0 such that '= is admissible in a logic L 2 NExtK i '0 =0 is
admissible in L.
Proof Observe rst that if ' and  do not contain p then '= is admissible
in L i ' ^ ( $ p)=p is admissible in L. So we can consider only rules of
the form '=p0 . Besides, without loss of generality we may assume that '
does not contain 2. With every non-atomic subformula  of ' we associate
the new variable p . For convenience we also put p = pi if  = pi and
p = ? if  = ?. We show now that the rule
p' ^ fp $ p1 $ p2 :  = 1 $ 2 2 Sub' $ 2 f^ _ !gg ^
fp $ 3p1 :  = 31 2 Sub'g=p0

^

^

152

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

is admissible in L i '=p0 is admissible in L. For brevity we denote the
antecedent of that rule by '00 .
()) Since every substitution instance of '00 =p0 is admissible in L, the
rule ' ^ 2 Sub' ( $ )=p0 and so '=p0 are also admissible in L.
(() Suppose '=p0 is admissible in L and '00 s is in L, for some substitution s = f =p :  2 Sub'g. By induction on the construction of 
one can readily show that  $ s 2 L. Therefore, ' $ 's 2 L. Since
'00 s 2 L, we must have p's = ' 2 L, from which 's 2 L and so p0 s 2 L.
Thus '00 =p0 is admissible in L.
The rule '00 =p0 is not reduced, but it is easy to make it so simply by
representing '00 in its full disjunctive normal form '0 , treating subformulas
3pi as variables.
2

V

W

From now on we will deal with only reduced rules di erent from ?=p0
(which is clearly admissible in any logic). Let j 'j =p0 be a reduced rule
in which every disjunct 'j is the conjunction of the form
:0 p0 ^ : : : ^ :m pm ^ :0 3p0 ^ : : : ^ :m 3pm

(17)

where each :i and :j is either blank or :. We will identify such conjunctions with the sets of their conjuncts. Now, given a non-empty set W of
conjunctions of the form (17), we dene a frame F = hW Ri and a model
M = hF Vi by taking

'i R'j i

8k 2 f0 : : :  mg(:3pk 2 'i ! :3pk 2 'j ^ :pk 2 'j ) ^
9k 2 f0 : : :  mg(:3pk 2 'j ^ 3pk 2 'i )

V(pk ) = f'i 2 W : pk 2 'i g:
It should be clear that F is nite, transitive and irreexive.
W
THEOREM 4.5 A reduced rule j 'j =p0 is not admissible in GL i there
is a model M = hF Vi dened as above on a set W of conjunctions of the

form (17) and such that
(i) :p0 2 'i for some 'i 2 W 
(ii) 'i j= 'i for every 'i 2 W 
(iii) for every antichain a in F there is 'j 2 W such that, for every
k 2 f0 : : :  mg, 'j j= 3pk i 'i j= 3+pk for some 'i 2 a.

Proof ()) We are given
W that there are formulas 0 : : :  m in variables
q1  : : :  qn such that j 'j 2 GL and p0 62 GL, where by W we de-

W

note f0 =p0 : : :  m =pmg. This is equivalent to MGL (n) j= j 'j and
MGL (n) 6j= p0 . Dene W to be the set of those disjuncts 'j in j 'j whose
substitution instances 'j are satised in MGL (n). Clearly W 6= . Let us
check (i) { (iii).

ADVANCED MODAL LOGIC

153

a point x in MGL (n) at which p is false. Since MGL (n) j=
Wj(i)'j ,Take
we must have x j= 'i for some i. One of the formulas p or :p is a
0

0

0

conjunct of 'i . Clearly it is not p0 . Therefore, :p0 2 'i .
(ii) It suces to show that, for all 'i 2 W and k 2 f0 : : :  mg, 'i j= 3pk
i 3pk 2 'i . Suppose 'i j= 3pk . Then there is 'j 2 W such that 'i R'j
and 'j j= pk . By the denition of V and R, this means that pk 2 'j
and 3pk 2 'i . Conversely, suppose 3pk 2 'i . Then x j= 'i and in
particular x j= 3pk for some x in MGL (n). Let y be a nal point in the set
fz 2 x": z j= pk g. Since MGL (n) is irreexive, we have y j= pk , y 6j= 3pk
and y j= 'j for some 'j 2 W . It follows that 'i R'j and 'j j= pk , from
which 'i j= 3pk .
(iii) Let a be an antichain in F. For every 'i 2 a, let xi be a nal point
in the set fy 2 WGL (n) : y j= 'i g. It should be clear that the points
fxi : 'i 2 ag form an antichain b in FGL (n) and so, by the construction of
FGL (n), there is a point y in FGL(n) such that y" = b". Then the formula
'j 2 W we are looking for is any one satisfying the condition y j= 'j , as
can be easily checked by a straightforward inspection.
(() The proof in this direction is rather technical we conne ourselves
to just a few remarks. Let M be a model satisfying (i){(iii). To prove that
j 'j =p0 is not admissible in GL we require once again the n-universal
model MGL (n), but this time we take n to be the number of symbols in the
rule. By induction on the depth of points in M one can show that M is a
generated submodel of MGL (n).
Our aim is to nd formulas 0  : : :  m such that MGL (n) j= j 'j and
MGL (n) 6j= p0 (here again  = f0 =p0  : : :  m =pm g). Loosely, we need
to extend the properties of M to the whole model MGL (n). To this end
we can take the sets f'i g in FGL(n) and augment them inductively in such
a way that we could embrace all points in FGL (n). At the induction step
we use the condition (iii), and the required 0  : : :  m are constructed with
the help of (i) and (ii) roughly, they describe in MGL (n) the analogues of
the truth-sets in M of the variables in our rule.
2

W

W

A remarkable feature of this criterion is that it can be e ectively checked.
Thus we have
THEOREM 4.6 There is an algorithm which, given an inference rule, can
decide whether it is admissible in GL.
In a similar way one can prove
THEOREM 4.7 (Rybakov 1987) The admissibility problem in Grz is decidable.

154

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

We show now that the admissibility problem in Int can be reduced to
the same problem in Grz and so is also decidable. To this end we require
the following
THEOREM 4.8 (Rybakov 1984b) A rule '= is admissible in Int i the
rule T (')=T () is admissible in Grz.
As a consequence of Theorems 4.7 and 4.8 we obtain
THEOREM 4.9 (Rybakov 1984b) The admissibility problem in Int is decidable.
Although there are many other examples of logics in which the admissibility problem is decidable and the scheme of establishing decidability is
quite similar to the argument presented above, proofs are rather dicult
and only in few cases they work for big families of logics as in Rybakov
1994]. Besides, all these results hold only for extensions of K4 and Int.
For logics with non-transitive frames, even for K, the admissibility problem
is still waiting for a solution. The same concerns polymodal, in particular
tense logics. Chagrov 1992b] constructed a decidable innitely axiomatizable logic in NExtK4 for which the admissibility problem is undecidable.
It would be of interest to nd modal and si-calculi of that sort.
A close algorithmic problem for a logic L is to determine, given an arbitrary formula '(p1  : : :  pn ), whether there exist formulas 1 ,. . . , n such
that '(1  : : :  n ) 2 L. Note that an "equation" '(p1  : : :  pn) has a solution in L i the rule '(p1  : : :  pn )=? is not admissible in L. This observation and Theorem 4.3 provide us with examples of logics in which the
substitution problem is decidable (see e.g. Rybakov 1993]). We do not
know, however, if there is a logic such that the substitution problem in it is
decidable, while the admissibility one is not.
The inference rules we have dealt with so far were structural in the sense
that they were \closed" under substitution. An interesting example of a
nonstructural rule was considered by Gabbay 1981a]:

' _ (2p ! p) where p 62 Sub' :
'
It is readily seen that this rule holds in a frame F (in the sense that for every
formula ' and every variable p not occurring in ', ' is valid in F whenever
(2p ! p) _ ' is valid in F) i F is irreexive and that K is closed under
it (since K is characterized by the class of irreexive frames). We refer the
reader to Venema 1991] for more information about rules of this type.

ADVANCED MODAL LOGIC

155

4.3 Properties of recursively axiomatizable logics

Dealing with innite classes of logics, we can regard questions like \Is a
logic L decidable?", \Does L have FMP?", etc., as mass algorithmic problems. But to formulate such problems properly we should decide rst how
to represent the input data of algorithms recognizing properties of logics.
One can, for instance, consider the class of recursively axiomatizable logics (which, by Craig's 1953] Theorem, coincides with that of recursively
enumerable ones) and represent them as programs generating their axioms.
However, this approach turns out to be too general because the following
analog of the Rice{Uspenskij Theorem holds.
THEOREM 4.10 (Kuznetsov) No nontrivial property of recursively axiomatizable si-logics is decidable.
Of course, nothing will change if we take some other family of logics, say
NExtK4. The proof of this theorem (Kuznetsov left it unpublished) is very
simple we give it even in a more general form than required.
PROPOSITION 4.11 Suppose L1 and L2 are logics in some family L, L1
is recursively axiomatizable, L1  L2 , L2 is nitely axiomatizable (say, by
a formula  ), and a property P holds for only one of L1 , L2 . Then no
algorithm can recognize P , given a program enumerating axioms of a logic
in L.

Proof Let 0 1  : : : be a recursive sequence of axioms for L1. Given an
arbitrary (Turing, Minsky, Pascal, etc.) program P having natural numbers
as its input, we dene the following recursive sequence of formulas (where
(n)1 and (n)2 are the rst and second components of the pair of natural
numbers with code n under some xed e ective encoding):

n if P does not come to a stop on input (n)1 in (n)2 steps
 otherwise.
This sequence axiomatizes L1 if P does not come to a stop on any input and
L2 otherwise. It is well known in recursion theory that the halting problem
is undecidable, and so the property P is undecidable in L as well.
2
n =

The reader must have already noticed that this proof has nothing to
do with modal and si-logics it is rather about e ective computations. To
avoid this unpleasant situation let us conne ourselves to the smaller class
of nitely axiomatizable modal and si-logics and try to nd algorithms recognizing properties of the corresponding calculi. However, even in this case
we should be very careful. If arbitrary nite axiomatizations are allowed
then we come across the following

156

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 4.12 (Kuznetsov 1963) For every nitely axiomatizable si-logic
L (in particular, Int, Cl, inconsistent logic), there is no algorithm which,
given an arbitrary nite list of formulas, can determine whether its closure
under substitution and modus ponens coincides with L.
Needless to say that the same holds for (normal) modal logics as well.
Fortunately, the situation is not so hopeless if we consider nite axiomatizations over some basic logics. For instance, by Makinson's Theorem,
one can e ectively recognize, given a formula ', whether the logic K  '
is consistent. Other examples of decidable properties in various lattices of
modal logics were presented in Theorems 1.89, 1.93, 1.101, and 2.37. In the
next section we consider those properties that turn out to be undecidable
in various classes of modal and si-calculi.

4.4 Undecidable properties of calculi
The rst \negative" algorithmic results concerning properties of modal calculi were obtained by Thomason 1982] who showed that FMP and Kripke
completeness are undecidable in NExtK, and consistency is undecidable in
NExtK:t. Later Thomason's discovery has been extended to other properties and narrower classes of logics. In fact, a good many standard properties
of modal and si-calculi (in reasonably big classes) proved to be undecidable
decidable ones are rather exceptional.
In this section we present three known schemes of proving such kind of
undecidability results. Each of them has its advantages (as well as disadvantages) and can be adjusted for various applications. The rst one is due
to Thomason 1982].
Let L(n) be a recursive sequence of normal bimodal calculi such that no
algorithm can decide, given n, whether L(n) is consistent. Such sequences,
as we shall see a bit later, exist even in NExtK4:t. Suppose also that L is
a normal unimodal calculus which does not have some property, say, FMP,
decidability or Kripke completeness. Consider now the recursive sequence of
logics L(n) & L with three necessity operators. If L(n) is inconsistent then
the fusion L(n) & L is inconsistent too and so has the properties mentioned
above. And if L(n) is consistent then, in accordance with Proposition 2.5,
L(n) & L is a conservative extension of both L(n) and L , which means
that it is Kripke incomplete, undecidable and does not have FMP whenever
L is so. Consequently, the three properties under consideration cannot be
decidable in the class NExtK3 , for otherwise the consistency of L(n) would
be decidable. By Theorem 2.18, these properties are undecidable in NExtK
as well. Note however that, since Thomason's simulation embeds polymodal
logics only into \non-transitive" unimodal ones, this very simple scheme

ADVANCED MODAL LOGIC

157

does not work if we want to investigate algorithmic aspects of properties of
calculi in NExtK4 and ExtInt.
To illustrate the second scheme let us recall the construction of the undecidable calculus in NExtK4:t discussed in Section 4.1. First, we choose a
Minsky program P and a conguration a = hs m ni so that no algorithm
can decide, given a conguration b, whether P : a ! b. (That they exist is
shown in Chagrov 1990b].) Then we put  = ? and add to K4:t  AxP
one more axiom
(: ^ #(s 1m  2n ) ! : ^ #(t 1k  2l )) ! 
where c = ht k li is an arbitrary xed conguration. The resulting calculus
is denoted by L(c). Suppose that P : a 6! c. Then one can readily check
that the new axiom is valid in the frame F shown in Fig. 19 and prove that
P : hs m ni ! ht0 k0 l0i i
: ^ #(s 1m  2n ) ! : ^ #(t0  1k  2l ) 2 L(c):
Therefore, L(c) is undecidable, consistent and does not have FMP. And if
P : a ! c then L(c) is clearly inconsistent. It follows by the choice of P and
a that consistency, decidability and FMP are undecidable in NExtK4:t. In
fact, the argument will change very little if we take as  the axiom of some
tabular logic in NExtK4:t. So we obtain
THEOREM 4.13 The properties of tabularity and coincidence with an arbitrary xed tabular logic (in particular, inconsistent) are undecidable in
NExtK4:t
Moreover, these results (except the consistency problem, of course) can
be transferred to logics in NExtK. We demonstrate this by an example
complete proofs can be found in Chagrov 1996].
We require the frame which results from that in Fig. 19 by adding to it
a reexive point c0 and an irreexive one c1 so that c1 sees all other points
save a and b and is seen itself only from a and b. As before, we denote the
frame by F.
PROPOSITION 4.14 Let  be a formula refutable at some point in F different from c0 and 3> 2 K  . Then the problem of deciding, for an
arbitrary formula ', whether K  ' = K   is undecidable.
Proof It should be clear that  contains at least one variable, say r, and
there are points in F at which r has distinct truth-values (under the valuation refuting ) c0 and c1 are then the only points in F where the formulas
3
3
0 = 2 r _ 2 :r and
2
2
1 = 3 0 ^ (r _ 3r _ 3 r ) ^ (:r _ 3:r _ 3 :r )
0

0

158

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

are true, respectively. Observe that from every point in F save c0 we can
reach all points in F by  3 steps. So we can take # = 33. The formulas
 and  should be replaced with  = 3 1 ^ 32 1 ,  = 3 1 ^ :32 1 which
(under the valuation refuting ) are true only at a and b, respectively. Now
consider the logic

L(c) = K  AxP  (: ^ #(s 1m  2n ) ! : ^ #(t 1k  2l )) ! :

If P : a ! c then L(c) = K  . And if P : a 6! c then, using the fact that
the set of points in F where  is refutable coincides with the set of points
from which every point of the form e(x y z ) is accessible by three steps,
one can show that F j= L(c) and so L(c) 6= K  .
2
Putting, for instance,  = 2p $ p, we obtain then that the problem of
coincidence with Log is undecidable in NExtK. Likewise one can prove the
following
THEOREM 4.15 (i) If a consistent nitely axiomatizable logic L is not a
union-splitting of NExtK then the axiomatization problem for L above K is
undecidable.
(ii) The properties of tabularity and coincidence with an arbitrary xed
consistent tabular logic are undecidable in NExtK.
(iii) The problem of coincidence with an arbitrary xed consistent calculus
in NExtD4 or in NExtGL is undecidable in NExtK.
(iv) The properties of tabularity and coincidence with an arbitrary xed
tabular (in particular, inconsistent) logic are undecidable in ExtK4.
Of the algorithmic problems concerning tabularity that remain open the
most intriguing are undoubtedly the tabularity and local tabularity problems in NExtK4. Note that a positive solution to the former implies a
positive solution to the latter.
Now we present the second scheme in a more general form used in Chagrov 1990b] and Chagrov and Zakharyaschev 1993]. Assume again that the
second conguration problem is undecidable for P and a, and let  be a
formula such that L0   has some property P , where L0 is the minimal logic
in the class under consideration. Associate with P , a and a conguration
b formulas AxP and (a b) such that (a b) 2 L0  AxP i P : a ! b.
Besides,  and AxP are chosen so that AxP 2 L0  . Now consider the
calculus
L(b) = L0  AxP  (a b) !   
where  is some formula such that  2 L0  . If P : a ! b then we clearly
have L(b) = L0   and so L(b) has P  but if P : a 6! b then the fact
that L(b) does not have P must be ensured by an appropriate choice of  .

ADVANCED MODAL LOGIC

159

(In the considerations above we did not need  , i.e., it was sucient to put
 = >). With the help of this scheme one can prove the following
THEOREM 4.16 (i) The properties of decidability, Kripke completeness as
well as FMP are undecidable in the classes ExtInt, (N)ExtGrz, (N)ExtGL.
(ii) The interpolation property is undecidable in (N)ExtGL.
(iii) Hallden completeness is undecidable in ExtInt, (N)ExtGrz, ExtS.
These and some other results of that sort can be found in Chagrov
1990b,c, 1994, 1996], Chagrova 1991], Chagrov and Zakharyaschev 1993,
1995b].
The third scheme was developed in Chagrova 1989, 1991] and Chagrov
and Chagrova 1995] for establishing the undecidability of certain rst order
properties of modal calculi (or formulas). The di erence of this scheme from
the previous one is that now we use calculi of the form
L(b) = L0  AxP  (a b) _ 
where AxP satises one more condition besides those mentioned above:
it must be rst order denable on Kripke frames for L0. If P : a ! b
then the formula AxP ^ ((a b) _  ) is equivalent to AxP in the class of
Kripke frames for L0 and so is rst order denable on that class or its any
subclass. And if P : a 6! b then by choosing an appropriate  one can
show that AxP ^ ((a b) _  ) is not rst order denable on, say, countable
Kripke frames for L0 , as in Chagrova 1989], or on nite frames for L0, as in
Chagrov and Chagrova 1995]. In this way the following theorem is proved:
THEOREM 4.17 (i) No algorithm is able to recognize the rst order denability of modal formulas on the class of Kripke frames for S4 and even the
rst order denability on countable (nite) Kripke frames for S4. The properties of rst order denability and denability on countable (nite) Kripke
frames of intuitionistic formulas are undecidable as well.
(ii) The set of modal or intuitionistic formulas that are rst order denable on countable (nite) frames but are not rst order denable on the
class of all (respectively, countable) Kripke frames mentioned in (i) is undecidable.
We conclude this section with two remarks. First, all undecidability
results above can be formulated in the stronger form of recursive inseparability. For instance, the set of inconsistent calculi in NExtK4:t and the
set of calculi without FMP are recursively inseparable. And second, some
properties are not only undecidable but the families of calculi having them
are not recursively enumerable for example, the set of consistent calculi in
NExtK4:t is not enumerable. However, for the majority of other properties
the problem of enumerability of the corresponding calculi is open.

160

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

4.5 Semantical consequence

So far we have dealt with only syntactical formalizations of logical entailment. However, sometimes a semantical approach is preferable. Say that a
formula ' is a semantical consequence of a formula  in a class of frames
C if ' is valid in all frames in C validating . (One can consider also the
local, i.e., point-wise variant of this relation.) Note that ' is a consequence
of  in the class of, say, Kripke frames for S4 i ' is a consequence of
(2p ! 22 p) ^ (2p ! p) ^  in the class of all Kripke frames. But the
consequence relation on nite frames is not expressible by modal formulas
(as was shown in Chagrov 1995], if (2p ! 22 p) ^ ' is valid in arbitrarily
large nite rooted frames then it is valid in some innite rooted frame as
well).
In parallel with constructing and proving the undecidability of modal and
si-calculi we can obtain the following
THEOREM 4.18 The semantical consequence relation in the class of all
(K4-, S4-, Int-) Kripke frames is undecidable. Moreover, if j= denotes one
of these relations then there is a formula  (a formula ') such that the set
f' :  j= 'g is undecidable.
In a sense, formulas  and ', for which f' :  j= 'g is undecidable are
analogous to undecidable calculi and formulas, respectively. However, this
analogy is far from being perfect: for every formula , the sets f' :  ` 'g
and f' :  ` 'g are recursively enumerable, which contrasts with
THEOREM 4.19 (Thomason 1975a) There exists a formula  such that
f' :  j= 'g is a complete +11 set.
Unfortunately, Thomason's 1974b, 1975b, 1975c] results have not been
transferred so far to transitive frames, although this does not seem to be
absolutely impossible.
Chagrov 1990a] (see also Chagrov and Chagrova 1995]) developed a technique for proving the analog of Theorem 4.18 for the consequence relation
on all (K4-, S4-, GL-, Int-) nite frames. Moreover, since this relation is
clearly enumerable, instead of \undecidable" one can use \not enumerable".

4.6 Complexity problems

Having proved that a given logic is decidable, we are facing the problem of
nding an optimal (in one sense or another) decision algorithm for it. The
complexity of decision algorithms for many standard modal and si-logics is
determined by the size of minimal frames separating formulas from those
logics. For instance, as was shown by Jaskowski (1936) and McKinsey

ADVANCED MODAL LOGIC

161

(1941), for every ' 62 S4 (or ' 62 Int) there is a frame F j= S4 with
 2jSub'j points such that F 6j= '. The same upper bound is usually
obtained by the standard ltration. Is it possible to reduce the exponential
upper bound to the polynomial one? This question was raised by Kuznetsov
1975] for Int. It turned out, however, that it concerns not only Int. First,
Kuznetsov observed (for the proof see Kuznetsov 1979]) that if the answer
to his question is positive, i.e., Int has polynomial FMP, then the problem
\Are Int and Cl polynomially equivalent?" has a positive solution as well.
(Logics L1 and L2 are polynomially equivalent if there are polynomial time
transformations f and g of formulas such that ' 2 L1 i f (') 2 L2 and
' 2 L2 i g(') 2 L1 .) Then Statman 1979] showed that the problem \' 2
Int?" is PSPACE -complete and so Kuznetsov's problem is equivalent to
one of the \hopeless" complexity problems, namely \NP = PSPACE ?".
Complexity function
For a logic L with FMP, we introduce the complexity function

fL(n) = lmax
min jFj 
(') n F =L


j

'62L F6j='

where l('), the length of ', is the number of subformulas in ' and jFj the
number of points in F. If there is a constant c such that

fL (n)  2cn (or fL (n)  nc or fL(n)  c  n)
L is said to have the exponential (respectively, polynomial or linear) nite
model property. The following result shows that Int does not have polynomial FMP.
THEOREM 4.20 (Zakharyaschev and Popov 1979) log2 fInt(n) * n.

Proof The exponential upper bound is well known and to establish the
lower one it is sucient to use the formulas

n =

^ ((:pi ! qi ) _ (pi ! qi ) ! qi) ! (:p ! q ) _ (p ! q ):

n;1
i=1

+1

+1

+1

+1

1

1

1

1

It is not hard to see that n 2= Int and every refutation frame for n contains
the full binary tree of depth n as a subframe.
2
Likewise the same result can be proved for many other standard superintuitionistic and modal logics whose FMP is established by the usual ltration and whose frames contain full binary trees of arbitrary nite depth.
Such are, for instance, KC, SL, K4, S4, GL. In the case of K the length of

162

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

formulas that play the role ofpn is not a linear but a square function of n,
which means that fK (n) 2 cn , for some constant c > 0, and so K does
not have polynomial FMP either. As was shown in Zakharyaschev 1996],
all conal subframe modal and si-logics have exponential FMP. It seems
plausible that log2 fL(n) * n for every consistent si-logic L di erent from
Cl and axiomatizable by formulas in one variable.
The construction of Theorem 4.20 does not work for logics whose frames
do not contain arbitrarily large full binary trees. Such are, for instance,
logics of nite width or of nite depth, and the following was proved in
Chagrov 1983].
THEOREM 4.21 (i) The minimal logics of width n < ! in NExtK4, NExtS4,
NExtGrz, NExtGL, ExtInt have polynomial FMP.
(ii) Lin and all logics containing S4.3 have linear FMP.
(iii) The minimal logics of depth n in NExtGrz, NExtGL, ExtInt have
polynomial FMP, with the power of the corresponding polynomial  n ; 1.
(iv) The minimal logics of depth n in NExtK4, NExtS4 have polynomial
FMP, with the power of the corresponding polynomial  n.
Proof (i) is proved by two ltrations. First, with the help of the standard
ltration one constructs a nite frame separating a formula ' from the given
logic L and then, using the selective ltration, extracts from it a polynomial
separation frame: it suces to take a point refuting ' and all maximal
points at which  is false, for some 2 2 Sub' (in the intuitionistic case
 !  2 Sub' should be considered). (ii) is proved analogously.
To illustrate the proof of (iii) and (iv), we consider the minimal logic L of
depth 3 in NExtGL. Suppose ' 2= L. Then there is a transitive irreexive
model M of depth  3 refuting ' at its root r. Let 2i , for 1  i  m, be
all \boxed" subformulas of '. For every i 2 f1 : : :  mg, we choose a point
refuting i , if it exists. And then we do the same in the set x", for every
chosen point x. Let M0 be the submodel formed by the selected points and
r. Clearly, it contains at most 1 + m + m2 points. And by induction on the
construction of formulas in Sub' one can easily show that M0 refutes ' at
r.
To prove the lower bound one can use the formulas
n
n
^
^
n = :( 2(pi ! pi ) ^ 2(qi ! qi ) ^
i=1

+1

i=1

+1

^n 3(3> ^ 2 (:pi ^ pi)) ^ 2(3? ! ^n 3(:qi ^ qi)))
+

i=1

+1

i=1

+1

which are not in L and every separation frame for which contains the full
n-ary tree of depth 3, i.e., at least 1 + n + n2 points.
2

ADVANCED MODAL LOGIC

a1


a2

-

a3

-   

an


-

b1

-

163

b2

-   

bf (n)


Figure 20.
However, even if frames for a logic with FMP do not contain full nite
binary trees its complexity function can grow very fast, witness the following
result of Chagrov 1985a].
THEOREM 4.22 For every arithmetic function f (n), there are logics L of
width 1 in NExtK4 and of width 2 in ExtInt, NExtGrz, NExtGL having
FMP and such that fL (n) f (n).
Proof We construct a logic L 2 NExtK4:3 whose complexity function
grows faster than a given increasing arithmetic function f (n). Dene L to
be the logic of all frames of the form shown in Fig. 20. To see that L satises
the property we need, consider the sequence of formulas
1 = p1 _ 2(2p1 ! (2(2p ! p) ! p))
i+1 = pi+1 _ 2(2pi+1 ! i ):
Since these formulas are refuted at points of the form aj in suciently large
frames depicted in Fig. 20, they are not in L. And since L contains the
formulas
:n ! 3(3f (n);1> ^ 2f (n) ?)
n cannot be separated from L by a frame with  f (n) points.
2
For logics of nite depth this theorem does not hold, since according
to the description of nitely generated universal frames in Section 1.2, for
every L 2 NExtK4BDk (k 3), we have

fL (n)  22





2c n



k;2

for some constant c > 0. And as was shown in Chagrov 1985a], one cannot
in general reduce this upper bound.
THEOREM 4.23 For every k 3, there are logics L of depth k in NExtGrz,
NExtGL, ExtInt such that

fL(n) 22





2n



k;2 :

164

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Proof We illustrate the proof for k = 3 in NExtGL. Let L be the logic
characterized by the class of rooted frames Fm for GL of depth 3 dened

as follows. Fm contains m dead ends, every non-empty set of them has a
focus, i.e., a point that sees precisely the dead ends in this set, and besides
the root there are no other points in Fm. It should be clear that L does not
contain the formulas

m =

^n 2(pi ! pi) ! ^n 22(pi ! pi ):
+1

i=1

+1

i=1

On the other hand n is not refutable in a frame for L with < 2m points
because the following formulas are in L:
:m !

^

X f1:::mgX 6=

3(

^ 3 i^ ^

i2X

where i = p1 ^ : : : ^ pi ^ :pi+1 ^ : : : ^ :pm+1 .

i62X1im

:3 i)

2

Note, however, that the logics constructed in the proofs of the last two
theorems are not nitely axiomatizable. We know of only one \very complex" calculus with FMP.
THEOREM 4.24 log2 log2 fKP (n) * n.
For the proof see Chagrov and Zakharyaschev 1997], where the reader
can nd also some other results in this direction.
Relation to complexity classes
Let us return to the original problem of optimizing decision algorithms for
the logics under consideration. First of all, it is to be noted that there is
a natural lower bound for decision algorithms which cannot be reduced|
we mean the complexity of decision procedures for Cl. This is clear for
(consistent) modal logics on the classical base and by Glivenko's Theorem,
every si-logic \contains" Cl in the form of the negated formulas. Thus,
if we manage to construct an e ective decision procedure for some of our
logics then Cl can be decided by an equally e ective algorithm. (We remind
the reader that all existing decision algorithms for Cl require exponential
time (of the number of variables in the tested formulas). On the other
hand, only polynomial time algorithms are regarded to be acceptable in
complexity theory.)
So, when analyzing the complexity of decision algorithms for modal and
si-logics, it is reasonable to compare them with decision algorithms for Cl.
For example, if a logic L is polynomially equivalent to Cl then we can regard

ADVANCED MODAL LOGIC

165

these two logics to be of the same complexity. Moreover, provided that
somebody nds a polynomial time decision procedure for Cl, a polynomial
time decision algorithm can be constructed for L as well. The following
theorem lists results obtained by Ladner 1977], Ono and Nakamura 1980],
Chagrov 1983], and Spaan 1993].
THEOREM 4.25 All logics mentioned in the formulation of Theorem 4.21
are polynomially equivalent to Cl.

Proof We illustrate the proof only for the minimal logic L of depth 3 in
NExtGL using the method of Kuznetsov 1979]. Suppose ' is a formula
of length n. By Theorem 4.21, the condition ' 62 L means that M 6j= ',
for some model M = hF Vi based on a frame F for GL of depth  3 and

cardinality  c  n2 . We describe this observation by means of classical
formulas, understanding their variables as follows. Let x, y, z be names
(numbers) of points in F, for 1  x y z  c  n2 . With every pair hx yi of
points in F we associate a variable pxy whose meaning is \x sees y". And
with every  2 Sub' and every x we associate a variable qx which means
\ is true at x". Denote by  the conjunction
q1' ^ q2' ^ : : : ^ qc'n2 :

It means that ' is true in M. And let  be the conjunction of the following
formulas under all possible values of their subscripts:
:pxx  pxy ^ pyz ! pxz  qx: $ :qx 

qx^ $ qx ^ qx 

qx_ $ qx _ qx 

qx2 $

^ (pxy ! q ):

cn2

y=1

y

(The rst two formulas say that R is irreexive and transitive and the rest
simulate the truth-relation in M.) Finally, we dene a formula saying that
our frame is of depth  3:

=

^

1xyzucn2

:(pxy ^ pyz ^ pzu ):

The formula  ^ ^: is of length  50(cn2)5 and can be clearly constructed
by an algorithm working at most linear time of the length of '. It is readily
seen that ' 62 L i  ^  ^: is satisable in Cl. Thus we have polynomially
reduced the derivability problem in L to that in Cl. Since the converse
reduction is trivial, L and Cl are polynomially equivalent.
2
The reader must have noticed that Theorem 4.25 lists almost all logics
known to have polynomial FMP. Kuznetsov 1975] conjectured that every

166

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

calculus having polynomial FMP is polynomially equivalent to Cl. This
conjecture is closely related to some problems in the complexity theory of
algorithms. We remind the reader that NP is the class of problems that
can be solved by polynomial time algorithms on nondeterministic (Turing)
machines. An NP -complete problem is a problem in NP to which all other
problems in NP are polynomially reducible. (For more detailed denitions
consult Garey and Johnson 1979].) The most popular NP -complete problem is the satisability problem for Boolean formulas, i.e., the nonderivability problem for Cl. So the nonderivability problem for all logics listed
Theorem 4.25 is NP -complete and Kuznetsov's conjecture is equivalent to
a positive solution to the problem whether the nonderivability problem for
every calculus with polynomial FMP is NP -complete.
Note that if coNP = NP (for the denition of the class coNP see
Garey and Johnson 1979] we just mention that the derivability problem
in Cl is coNP -complete) then Kuznetsov's conjecture does hold. But
since \coNP = NP ?" belongs to the list of \unsolvable" problems under the current state of knowledge, it may be of interest to nd out whether
Kuznetsov's conjecture implies coNP = NP .
Another complexity class we consider here is the class PSPACE of
problems that can be solved by polynomial space algorithms. A typical
example of a PSPACE -complete problem is the truth problem for quantied Boolean formulas. The following theorem (which summarizes results
obtained by Ladner 1977], Statman 1979], Chagrov 1985a], Halpern and
Moses 1992] and Spaan 1993]) lists some PSPACE -complete logics.
THEOREM 4.26 The nonderivability problem (and so the derivability problem) in the following logics is PSPACE -complete: Int, KC, K, K & K,
S4, S4 & S4, S5 & S5, GL, Grz, K:t and K4:t.
It follows in particular that complexity is not preserved under the formation of fusions of logics (under the assumption NP 6= PSPACE ),
since nonderivability in S5 is NP -complete. For more information on the
preservation of complexity under fusions consult Spaan 1993].
Finally we note that the nonderivability problem in logics with the universal modality or common knowledge operator is mostly even EXPTIME complete, witness Ku Spaan 1993] and S4EC2 Halpern and Moses 1992].
5 APPENDIX
We conclude this chapter with a (by no means complete) list of references for
those directions of research in modal logic that were not considered above:
 Congruential logics. These are modal logics that do not necessarily contain the distribution axiom 2(p ! q) ! (2p ! 2q) but are

ADVANCED MODAL LOGIC

167

closed under modus ponens and the congruence rule p $ q=2p $ 2q.
Segerberg 1971] and Chellas 1980] dene a semantics for these logics
Lewis 1974] proves FMP of all congruential non-iterative logics and
Surendonk 1996] shows that they are canonical. Do)sen 1988] considers duality between algebras and neighbourhood frames and Kracht
and Wolter 1997a] study embeddings into normal bimodal logics.
 Modal logics with graded modalities. The truth-relation for their possibility operators 3n is dened as follows: x j= 3np i there exist at
least n points accessible from x at which p holds. An early reference
is Fine 1972] more recent are van der Hoek 1992] (applications to
epistemic logic) and Cerrato 1994] (FMP and decidability).
 Modal logics with the dierence operator or with nominals (or names).
The semantics of nominals is similar to that of propositional variables
the di erence is that a nominal is true at exactly one point in a frame.
For the di erence operator 6=], we have x j= 6=]p i p is true everywhere except x. De Rijke 1993], Blackburn 1993] and Goranko and
Gargov 1993] study the completeness and expressive power of systems
of that sort. Closely related to the di erence operator is the modal
operator i] for inaccessible worlds: x j= i]p i p is true in all worlds
which are not accessible from x, see Humberstone 1983] and Goranko
1990a].
 Modal logics with dyadic or even polyadic operators. For duality theory
in this case see Goldblatt 1989]. An extensive study of Sahlqvisttype theorems with applications to polyadic logics is Venema 1991].
For connections with the theory of relational algebras see Mikulas
1995] and Marx 1995]. In those dissertations the reader can nd also
recent results on arrow logic, i.e., a certain type of polyadic logic which
is interpreted in Kripke frames built from arrows. An embedding
of polyadic logics into polymodal logics is discussed in Kracht and
Wolter 1997b].
 Bisimulations. Bisimulations were introduced in modal logic by van
Benthem 1983] to characterize its expressive power see also de Rijke
1996]. Visser 1996] used bisimulations to prove uniform interpolation.
Recently, bisimulations have attracted attention because they form a
common tool in modal logic and process theory. We refer the reader
to collection Ponse et al. 1996] for information on this subject.
 Modal logics with xed point operators, i.e., modal logics enriched by
operators forming the least and greatest xed points of monotone
formulas. These systems are also called modal -calculi. Under this

168

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

name they were introduced and studied by Kozen 1983, 1988] see
also Walukiewicz 1993, 1996] and Bosangue and Kwiatkowska 1996].
 Proof theory. Early references to studies of sequent calculi and natural
deduction systems for a few modal logics can be found in Basic Modal
Logic. More recently, (non-standard) sequent calculi for modal logics have been considered by Do)sen 1985b], Masini 1992] and Avron
1996] see also collection Wansing 1996] and the chapter Sequent
systems for modal logics in this Handbook. For natural deduction
systems see Borghuis 1993] tableau systems for modal and tense
logics were constructed in Fitting 1983], Rautenberg 1983], Gore
1994] and Kashima 1994]. Orlowska 1996] develops relational proof
systems. Display calculi for modal logics were introduced by Belnap
1982] see also Wansing 1994] and collection Wansing 1996].

REFERENCES
Amati and Pirri, 1994] G. Amati and F. Pirri. A uniform tableau method for intuitionistic modal logics I. Studia Logica, 53:29{60, 1994.
Anderson, 1972] J.G. Anderson. Superconstructive propositional calculi with extra axiom schemes containing one variable. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 18:113{130, 1972.
Avron, 1996] A. Avron. The method of hypersequents in the proof therory of propositional non-classical logics. In W. Hodges, M. Hyland, C. Steinhorn, and J. Truss,
editors, Logic: from Foundations to Applications, pages 1{32. Clarendon Press, Oxford, 1996.
Barwise and Moss, 1996] J. Barwise and L. Moss. Vicious Circles. CSLI Publications,
Stanford, 1996.
Beklemishev, 1994] L.D. Beklemishev. On bimodal logics of provability. Annals of Pure
and Applied Logic, 68:115{159, 1994.
Beklemishev, 1996] L.D. Beklemishev. Bimodal logics for extensions of arithmetical
theories. Journal of Symbolic Logic, 61:91{124, 1996.
Bellissima, 1984] F. Bellissima. Atoms in modal algebras. Zeitschrift fur Mathematische
Logik und Grundlagen der Mathematik, 30:303{312, 1984.
Bellissima, 1985] F. Bellissima. An eective representation for nitely generated free
interior algebras. Algebra Universalis, 20:302{317, 1985.
Bellissima, 1988] F. Bellissima. On the lattice of extensions of the modal logic K:Altn .
Archive of Mathematical Logic, 27:107{114, 1988.
Bellissima, 1991] F. Bellissima. Atoms of tense algebras. Algebra Universalis, 28:52{78,
1991.
Belnap, 1982] N.D. Belnap. Display logic. Journal of Philosophical Logic, 11:375{417,
1982.
Beth, 1953] E.W. Beth. On Padua's method in the theory of denitions. Indagationes
Mathematicae, 15:330{339, 1953.
Bezhanishvili, 1997] G. Bezhanishvili. Modal intuitionistic logics and superintuitionistic
predicate logics: correspondence theory. Manuscript, 1997.
Blackburn, 1993] P. Blackburn. Nominal tense logic. Notre Dame Journal of Formal
Logic, 34:56{83, 1993.
Blok and Kohler, 1983] W.J. Blok and P. Kohler. Algebraic semantics for quasi-classical
modal logics. Journal of Symbolic Logic, 48:941{964, 1983.

ADVANCED MODAL LOGIC

169

Blok and Pigozzi, 1982] W. Blok and D. Pigozzi. On the structure of varieties with
equationally denable principal congruences I. Algebra Universalis, 15:195{227, 1982.
Blok, 1976] W.J. Blok. Varieties of interior algebras. PhD thesis, University of Amsterdam, 1976.
Blok, 1978] W.J. Blok. On the degree of incompleteness in modal logics and the covering relation in the lattice of modal logics. Technical Report 78-07, Department of
Mathematics, University of Amsterdam, 1978.
Blok, 1980a] W.J. Blok. The lattice of modal algebras is not strongly atomic. Algebra
Universalis, 11:285{294, 1980.
Blok, 1980b] W.J. Blok. The lattice of modal logics: an algebraic investigation. Journal
of Symbolic Logic, 45:221{236, 1980.
Blok, 1980c] W.J. Blok. Pretabular varieties of modal algebras. Studia Logica, 39:101{
124, 1980.
Boolos, 1993] G. Boolos. The Logic of Provability. Cambridge University Press, 1993.
Borghuis, 1993] T. Borghuis. Interpreting modal natural deduction in type theory. In
M. de Rijke, editor, Diamonds and Defaults, pages 67{102. Kluwer Academic Publishers, 1993.
Bosangue and Kwiatkowska, 1996] M. Bosangue and M. Kwiatkowska. Re-interpreting
the modal -calculus. In A. Ponse, M. de Rijke, and Y. Venema, editors, Modal Logic
and Process Algebra, pages 65{83. CSLI publications, Stanford, 1996.
Bozic and Dosen, 1984] M. Bozic and K. Dosen. Models for normal intuitionistic logics.
Studia Logica, 43:217{245, 1984.
Buchi and Siefkes, 1973] J.R. Buchi and D. Siefkes. The monadic second order theory
of all countable ordinals. Number 328 in Lecture Notes in Mathematics. Springer,
1973.
Buchi, 1962] J.R. Buchi. On a decision method in restricted second order arithmetic. In
Logic, Methodology and Philosophy of Science: Proceedings of the 1960 International
Congress, pages 1{11. Stanford University Press, 1962.
Bull, 1966a] R.A. Bull. MIPC as the formalization of an intuitionistic concept of
modality. Journal of Symbolic Logic, 31:609{616, 1966.
Bull, 1966b] R.A. Bull. That all normal extensions of S 4:3 have the nite model property. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 12:341{
344, 1966.
Bull, 1968] R.A. Bull. An algebraic study of tense logic with linear time. Journal of
Symbolic Logic, 33:27{38, 1968.
Cerrato, 1994] C. Cerrato. Decidability by ltrations for graded normal logics. Studia
Logica, 53:61{73, 1994.
Chagrov and Chagrova, 1995] A.V. Chagrov and L.A. Chagrova. Algorithmic problems
concerning rst order denability of modal formulas on the class of all nite frames.
Studia Logica, 55:421{448, 1995.
Chagrov and Zakharyaschev, 1991] A.V. Chagrov and M.V. Zakharyaschev. The disjunction property of intermediate propositional logics. Studia Logica, 50:63{75, 1991.
Chagrov and Zakharyaschev, 1992] A.V. Chagrov and M.V. Zakharyaschev. Modal
companions of intermediate propositional logics. Studia Logica, 51:49{82, 1992.
Chagrov and Zakharyaschev, 1993] A.V. Chagrov and M.V. Zakharyaschev. The undecidability of the disjunction property of propositional logics and other related problems. Journal of Symbolic Logic, 58:49{82, 1993.
Chagrov and Zakharyaschev, 1995a] A.V. Chagrov and M.V. Zakharyaschev. On the
independent axiomatizability of modal and intermediate logics. Journal of Logic and
Computation, 5:287{302, 1995.
Chagrov and Zakharyaschev, 1995b] A.V. Chagrov and M.V. Zakharyaschev. Sahlqvist
formulas are not so elementary even above S 4. In L. Csirmaz, D.M. Gabbay, and
M. de Rijke, editors, Logic Colloquium'92, pages 61{73. CSLI Publications, Stanford,
1995.
Chagrov and Zakharyaschev, 1997] A.V. Chagrov and M.V. Zakharyaschev. Modal
Logic. Oxford University Press, 1997.

170

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Chagrov, 1983] A.V. Chagrov. On the polynomial approximability of modal and superintuitionistic logics. In Mathematical Logic, Mathematical Linguistics and Algorithm
Theory, pages 75{83. Kalinin State University, Kalinin, 1983. (Russian).
Chagrov, 1985a] A.V. Chagrov. On the complexity of propositional logics. In Complexity Problems in Mathematical Logic, pages 80{90. Kalinin State University, Kalinin,
1985. (Russian).
Chagrov, 1985b] A.V. Chagrov. Varieties of logical matrices. Algebra and Logic, 24:278{
325, 1985.
Chagrov, 1989] A.V. Chagrov. Nontabularity|pretabularity, antitabularity, coantitabularity. In Algebraic and Logical Constructions, pages 105{111. Kalinin State
University, Kalinin, 1989. (Russian).
Chagrov, 1990a] A.V. Chagrov. Undecidability of the nitary semantical consequence.
In Proceedings of the XXth USSR Conference on Mathematica Logic, Alma-Ata, page
162, 1990. (Russian).
Chagrov, 1990b] A.V. Chagrov. Undecidable properties of extensions of provability
logic. I. Algebra and Logic, 29:231{243, 1990.
Chagrov, 1990c] A.V. Chagrov. Undecidable properties of extensions of provability
logic. II. Algebra and Logic, 29:406{413, 1990.
Chagrov, 1992a] A.V. Chagrov. Continuality of the set of maximal superintuitionistic
logics with the disjunction property. Mathematical Notes, 51:188{193, 1992.
Chagrov, 1992b] A.V. Chagrov. A decidable modal logic with the undecidable admissibility problem for inference rules. Algebra and Logic, 31:53{55, 1992.
Chagrov, 1994] A.V. Chagrov. Undecidable properties of superintuitionistic logics. In
S.V. Jablonskij, editor, Mathematical Problems of Cybernetics, volume 5, pages 67{
108. Physmatlit, Moscow, 1994. (Russian).
Chagrov, 1995] A.V. Chagrov. One more rst-order eect in Kripke semantics. In
Proceedings of the 10th International Congress of Logic, Methodology and Philosophy
of Science, page 124, Florence, Italy, 1995.
Chagrov, 1996] A.V. Chagrov. Tabular modal logics: algorithmic problems.
Manuscript, 1996.
Chagrova, 1986] L.A. Chagrova. On the rst order denability of intuitionistic formulas with restrictions on occurrences of the connectives. In M.I. Kanovich, editor,
Logical Methods for Constructing E ective Algorithms, pages 135{136. Kalinin State
University, Kalinin, 1986. (Russian).
Chagrova, 1989] L.A. Chagrova. On the problem of de nability of propositional formulas of intuitionistic logic by formulas of classical rst order logic. PhD thesis, Kalinin
State University, 1989. (Russian).
Chagrova, 1990] L.A. Chagrova. On the preservation of rst order properties under the
embedding of intermediate logics into modal logics. In Proceedings of the Xth USSR
Conference for Mathematical Logic, page 163, 1990. (Russian).
Chagrova, 1991] L.A. Chagrova. An undecidable problem in correspondence theory.
Journal of Symbolic Logic, 56:1261{1272, 1991.
Chellas and Segerberg, 1994] B. Chellas and K. Segerberg. Modal logics with the
MacIntosh-rule. Journal of Philosophical Logic, 23:67{86, 1994.
Chellas, 1980] B.F. Chellas. Modal Logic: An Introduction. Cambridge University
Press, 1980.
Craig, 1953] W. Craig. On axiomatizability within a system. Journal of Symbolic Logic,
18:30{32, 1953.
Craig, 1957] W. Craig. Three uses of the Herbrandt{Gentzen theorem in relating model
theory and proof theory. Journal of Symbolic Logic, 22:269{285, 1957.
Cresswell, 1984] M.J. Cresswell. An incomplete decidable modal logic. Journal of Symbolic Logic, 49:520{527, 1984.
Day, 1977] A. Day. Splitting lattices generate all lattices. Algebra Universalis, 7:163{
170, 1977.
de Rijke, 1993] M. de Rijke. Extending Modal Logic. PhD thesis, Universiteit van
Amsterdam, 1993.

ADVANCED MODAL LOGIC

171

de Rijke, 1996] M. de Rijke. A Lindstrom theorem for modal logic. In A. Ponse,
M. de Rijke, and Y. Venema, editors, Modal Logic and Process Algebra, pages 217{230.
CSLI Publications, Stanford, 1996.
Diego, 1966] A. Diego. Sur les algebres de Hilbert. Gauthier-Villars, Paris, 1966.
Doets, 1987] K. Doets. Completeness and de nability. PhD thesis, Universiteit van
Amsterdam, 1987.
Dosen, 1985a] K. Dosen. Models for stronger normal intuitionistic modal logics. Studia
Logica, 44:39{70, 1985.
Dosen, 1985b] K. Dosen. Sequent-systems for modal logic. Journal of Symbolic Logic,
50:149{159, 1985.
Dosen, 1988] K. Dosen. Duality between modal algebras and neighbourhood frames.
Studia Logica, 48:219{234, 1988.
Drabbe, 1967] J. Drabbe. Une propriete des matrices caracteristiques des systemes S 1,
S 2, et S 3. Comptes Rendus de l'Academie des Sciences, Paris, 265:A1, 1967.
Dugundji, 1940] J. Dugundji. Note on a property of matrices for Lewis and Langford's
calculi of propositions. Journal of Symbolic Logic, 5:150{151, 1940.
Dummett and Lemmon, 1959] M.A.E. Dummett and E.J. Lemmon. Modal logics between S 4 and S 5. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 5:250{264, 1959.
Dummett, 1959] M.A.E. Dummett. A propositional calculus with denumerable matrix.
Journal of Symbolic Logic, 24:97{106, 1959.
Ershov, 1980] Yu.L. Ershov. Decision problems and constructive models. Nauka,
Moscow, 1980. (Russian).
Esakia and Meskhi, 1977] L.L. Esakia and V.Yu. Meskhi. Five critical systems. Theoria, 40:52{60, 1977.
Esakia, 1974] L.L. Esakia. Topological Kripke models. Soviet Mathematics Doklady,
15:147{151, 1974.
Esakia, 1979a] L.L. Esakia. On varieties of Grzegorczyk algebras. In A. I. Mikhailov, editor, Studies in Non-classical Logics and Set Theory, pages 257{287. Moscow, Nauka,
1979. (Russian).
Esakia, 1979b] L.L. Esakia. To the theory of modal and superintuitionistic systems. In
V.A. Smirnov, editor, Logical Inference. Proceedings of the USSR Symposium on the
Theory of Logical Inference, pages 147{172. Nauka, Moscow, 1979. (Russian).
Ewald, 1986] W.B. Ewald. Intuitionistic tense and modal logic. Journal of Symbolic
Logic, 51:166{179, 1986.
Ferrari and Miglioli, 1993] M. Ferrari and P. Miglioli. Counting the maximal intermediate constructive logics. Journal of Symbolic Logic, 58:1365{1408, 1993.
Ferrari and Miglioli, 1995a] M. Ferrari and P. Miglioli. A method to single out maximal
propositional logics with the disjunction property. I. Annals of Pure and Applied Logic,
76:1{46, 1995.
Ferrari and Miglioli, 1995b] M. Ferrari and P. Miglioli. A method to single out maximal
propositional logics with the disjunction property. II. Annals of Pure and Applied
Logic, 76:117{168, 1995.
Fine and Schurz, 1996] K. Fine and G. Schurz. Transfer theorems for stratied modal
logics. In J. Copeland, editor, Logic and Reality, Essays in Pure and Applied Logic.
In memory of Arthur Prior, pages 169{213. Oxford University Press, 1996.
Fine, 1971] K. Fine. The logics containing S 4:3. Zeitschrift fur Mathematische Logik
und Grundlagen der Mathematik, 17:371{376, 1971.
Fine, 1972] K. Fine. In so many possible worlds. Notre Dame Journal of Formal Logic,
13:516{520, 1972.
Fine, 1974a] K. Fine. An ascending chain of S 4 logics. Theoria, 40:110{116, 1974.
Fine, 1974b] K. Fine. An incomplete logic containing S 4. Theoria, 40:23{29, 1974.
Fine, 1974c] K. Fine. Logics containing K 4, part I. Journal of Symbolic Logic, 39:229{
237, 1974.
Fine, 1975a] K. Fine. Normal forms in modal logic. Notre Dame Journal of Formal
Logic, 16:31{42, 1975.

172

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Fine, 1975b] K. Fine. Some connections between elementary and modal logic. In
S. Kanger, editor, Proceedings of the Third Scandinavian Logic Symposium, pages
15{31. North-Holland, Amsterdam, 1975.
Fine, 1985] K. Fine. Logics containing K 4, part II. Journal of Symbolic Logic, 50:619{
651, 1985.
Fischer-Servi, 1977] G. Fischer-Servi. On modal logics with an intuitionistic base. Studia Logica, 36:141{149, 1977.
Fischer-Servi, 1980] G. Fischer-Servi. Semantics for a class of intuitionistic modal calculi. In M. L. Dalla Chiara, editor, Italian Studies in the Philosophy of Science, pages
59{72. Reidel, Dordrecht, 1980.
Fischer-Servi, 1984] G. Fischer-Servi. Axiomatizations for some intuitionistic modal
logics. Rend. Sem. Mat. Univers. Polit., 42:179{194, 1984.
Fitting, 1983] M. Fitting. Proof Methods for Modal and Intuitionistic Logics. Reidel,
Dordrecht, 1983.
Font, 1984] J. Font. Implication and deduction in some intuitionistic modal logics.
Reports on Mathematical logic, 17:27{38, 1984.
Font, 1986] J. Font. Modality and possibility in some intuitionistic modal logics. Notre
Dame Journal of Formal Logic, 27:533{546, 1986.
Friedman, 1975] H. Friedman. One hundred and two problems in mathematical logic.
Journal of Symbolic Logic, 40:113{130, 1975.
Fuhrmann, 1989] A. Fuhrmann. Models for relevant modal logics. Studia Logica,
49:502{514, 1989.
Gabbay and de Jongh, 1974] D.M. Gabbay and D.H.J. de Jongh. A sequence of decidable nitely axiomatizable intermediate logics with the disjunction property. Journal
of Symbolic Logic, 39:67{78, 1974.
Gabbay et al., 1994] D. Gabbay, I. Hodkinson, and M. Reynolds. Temporal Logic:
Mathematical Foundations and Computational Aspects, Volume 1. Oxford University Press, 1994.
Gabbay, 1970] D.M. Gabbay. The decidability of the Kreisel{Putnam system. Journal
of Symbolic Logic, 35:431{436, 1970.
Gabbay, 1971] D.M. Gabbay. On decidable, nitely axiomatizable modal and tense
logics without the nite model property. I, II. Israel Journal of Mathematics, 10:478{
495, 496{503, 1971.
Gabbay, 1972] D.M. Gabbay. Craig's interpolation theorem for modal logics. In
W. Hodges, editor, Proceedings of logic conference, London 1970, volume 255 of Lecture Notes in Mathematics, pages 111{127. Springer-Verlag, Berlin, 1972.
Gabbay, 1975] D.M. Gabbay. Decidability results in non-classical logics. Annals of
Mathematical Logic, 8:237{295, 1975.
Gabbay, 1976] D.M. Gabbay. Investigations into Modal and Tense Logics, with Applications to Problems in Linguistics and Philosophy. Reidel, Dordrecht, 1976.
Gabbay, 1981a] D.M. Gabbay. An irreexivity lemma with application to axiomatizations of conditions on linear frames. In U. Monnich, editor, Aspects of Philosophical
Logic, pages 67{89. Reidel, Dordrecht, 1981.
Gabbay, 1981b] D.M. Gabbay. Semantical Investigations in Heyting's Intuitionistic
Logic. Reidel, Dordrecht, 1981.
Galanter, 1990] G.I. Galanter. A continuum of intermediate logics which are maximal
among the logics having the intuitionistic disjunctionless fragment. In Proceedings of
10th USSR Conference for Mathematical Logic, page 41, Alma{Ata, 1990. (Russian).
Garey and Johnson, 1979] M.R. Garey and D.S. Johnson. Computers and intractability. A guide to the theory of NP-completeness. Freemann, San Franzisco, 1979.
Gargov and Passy, 1990] G. Gargov and S. Passy. A note on Boolean modal logic. In
P. Petkov, editor, Mathematical Logic, pages 299{309. Plenum Press, 1990.
Gargov et al., 1987] G. Gargov, S. Passy, and T. Tinchev. Modal environment for
Boolean speculations. In D. Skordev, editor, Mathematical Logic and its Applications,
pages 253{263. Plenum Press, 1987.

ADVANCED MODAL LOGIC

173

Gentzen, 1934{35] G. Gentzen. Untersuchungen uber das logische Schliessen. Mathematische Zeitschrift, 39:176{210, 405{431, 1934{35.
Ghilardi and Meloni, 1997] S. Ghilardi and G. Meloni. Constructive canonicity in nonclassical logics. Annals of Pure and Applied Logic, 1997. To appear.
Ghilardi and Zawadowski, 1995] S. Ghilardi and M. Zawadowski. Undenability of
propositional quantiers in modal system S 4. Studia Logica, 55:259{271, 1995.
Ghilardi, 1995] S. Ghilardi. An algebraic theory of normal forms. Annals of Pure and
Applied Logic, 71:189{245, 1995.
Godel, 1932] K. Godel. Zum intuitionistischen Aussagenkalkul. Anzeiger der Akademie
der Wissenschaften in Wien, 69:65{66, 1932.
Godel, 1933] K. Godel. Eine Interpretation des intuitionistischen Aussagenkalkuls.
Ergebnisse eines mathematischen Kolloquiums, 4:39{40, 1933.
Goldblatt and Thomason, 1974] R.I. Goldblatt and S.K. Thomason. Axiomatic classes
in propositional modal logic. In J. Crossley, editor, Algebraic Logic, Lecture Notes in
Mathematics vol. 450, pages 163{173. Springer, Berlin, 1974.
Goldblatt, 1976a] R.I. Goldblatt. Metamathematics of modal logic, Part I. Reports on
Mathematical Logic, 6:41{78, 1976.
Goldblatt, 1976b] R.I. Goldblatt. Metamathematics of modal logic, Part II. Reports
on Mathematical Logic, 7:21{52, 1976.
Goldblatt, 1987] R.I. Goldblatt. Logics of Time and Computation. Number 7 in CSLI
Lecture Notes, Stanford. CSLI, 1987.
Goldblatt, 1989] R.I. Goldblatt. Varieties of complex algebras. Annals of Pure and
Applied Logic, 38:173{241, 1989.
Goldblatt, 1995] R.I. Goldblatt. Elementary generation and canonicity for varieties of
boolean algebras with operators. Algebra Universalis, 34:551{607, 1995.
Goranko and Gargov, 1993] V. Goranko and G. Gargov. Modal logic with names. Journal of Philosophical Logic, 22:607{636, 1993.
Goranko and Passy, 1992] V. Goranko and S. Passy. Using the universal modality:
Gains and questions. Journal of Logic and Computation, 2:5{30, 1992.
Goranko, 1990a] V. Goranko. Completeness and incompleteness in the bimodal base
L(R ;R). In P. Petkov, editor, Mathematical Logic, pages 311{326. Plenum Press,
1990.
Goranko, 1990b] V. Goranko. Modal denability in enriched languages. Notre Dame
Journal of Formal Logic, 31:81{105, 1990.
Gore, 1994] R. Gore. Cut-free sequent and tableau systems for propositional Diodorian
modal logics. Studia Logica, 53:433{458, 1994.
Grefe, 1994] C. Grefe. Modale Logiken funktionaler Frames. Master's thesis, Department of Mathematics, Freie Universitat Berlin, 1994.
Grefe, 1997] C. Grefe. Fischer Servi's intuitionistic modal logic has the nite model
property. In M. Kracht, M. De Rijke, H. Wansing, and M. Zakharyaschev, editors,
Advances in Modal Logic. CSLI, Stanford, 1997.
Halpern and Moses, 1992] J. Halpern and Yo. Moses. A guide to completeness and
complexity for modal logics of knowledge and belief. Arti cial Intelligence, 54:319{
379, 1992.
Harrop, 1958] R. Harrop. On the existence of nite models and decision procedures for
propositional calculi. Proceedings of the Cambridge Philosophical Society, 54:1{13,
1958.
Hemaspaandra, 1996] E. Hemaspaandra. The price of universality. Notre Dame Journal
of Formal Logic, 37:174{203, 1996.
Hosoi and Ono, 1973] T. Hosoi and H. Ono. Intermediate propositional logics (A survey). Journal of Tsuda College, 5:67{82, 1973.
Hosoi, 1967] T. Hosoi. On intermediate logics. Journal of the Faculty of Science,
University of Tokyo, 14:293{312, 1967.
Hughes and Cresswell, 1984] G.E. Hughes and M.J. Cresswell. A Companion to Modal
Logic. Methuen, London, 1984.

174

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Humberstone, 1983] I.L. Humberstone. Inaccessible worlds. Notre Dame Journal of
Formal Logic, 24:346{352, 1983.
Isard, 1977] S. Isard. A nitely axiomatizable undecidable extension of K . Theoria,
43:195{202, 1977.
Janiczak, 1953] A. Janiczak. Undecidability of some simple formalized theories. Fundamenta Mathematicae, 40:131{139, 1953.
Jankov, 1963] V.A. Jankov. The relationship between deducibility in the intuitionistic
propositional calculus and nite implicational structures. Soviet Mathematics Doklady, 4:1203{1204, 1963.
Jankov, 1968a] V.A. Jankov. The calculus of the weak \law of excluded middle". Mathematics of the USSR, Izvestiya, 2:997{1004, 1968.
Jankov, 1968b] V.A. Jankov. The construction of a sequence of strongly independent superintuitionistic propositional calculi. Soviet Mathematics Doklady, 9:806{807, 1968.
Jankov, 1969] V.A. Jankov. Conjunctively indecomposable formulas in propositional
calculi. Mathematics of the USSR, Izvestiya, 3:17{35, 1969.
Jaskowski, 1936] S. Jaskowski. Recherches sur le systeme de la logique intuitioniste. In
Actes Du Congres Intern. De Phil. Scienti que. VI. Phil. Des Mathematiques, Act.
Sc. Et Ind 393, Paris, pages 58{61, 1936.
Jipsen and Rose, 1993] P. Jipsen and H. Rose. Varieties of Lattices. 1993.
Jonsson and Tarski, 1951] B. Jonsson and A. Tarski. Boolean algebras with operators.
I. American Journal of Mathematics, 73:891{939, 1951.
Jonsson, 1994] B. Jonsson. On the canonicity of Sahlqvist identities. Studia Logica,
53:473{491, 1994.
Kashima, 1994] R. Kashima. Cut-free sequent calculi for some tense logics. Studia
Logica, 53:119{136, 1994.
Kirk, 1982] R.E. Kirk. A result on propositional logics having the disjunction property.
Notre Dame Journal of Formal Logic, 23:71{74, 1982.
Kleene, 1945] S. Kleene. On the interpretation of intuitionistic number theory. Journal
of Symbolic Logic, 10:109{124, 1945.
Kleyman, 1984] Yu.G. Kleyman. Some questions in the theory of varieties of groups.
Mathematics of the USSR, Izvestiya, 22:33{65, 1984.
Koppelberg, 1988] S. Koppelberg. General theory of Boolean algebras. In J. Monk,
editor, Handbook of Boolean Algebras, volume 1. North-Holland, Amsterdam, 1988.
Kozen, 1983] D. Kozen. Results on the propositional -calculus. Theoretical Computer
Science, 27:333{354, 1983.
Kozen, 1988] D. Kozen. A nite model theorem for the propositional -calculus. Studia
Logica, 47:234{241, 1988.
Kracht and Wolter, 1991] M. Kracht and F. Wolter. Properties of independently axiomatizable bimodal logics. Journal of Symbolic Logic, 56:1469{1485, 1991.
Kracht and Wolter, 1997a] M. Kracht and F. Wolter. Normal monomodal logics can
simulate all others. Journal of Symbolic Logic, 1997. To appear.
Kracht and Wolter, 1997b] M. Kracht and F. Wolter. Simulation and transfer results
in modal logic: A survey. Studia Logica, 1997. To appear.
Kracht, 1990] M. Kracht. An almost general splitting theorem for modal logic. Studia
Logica, 49:455{470, 1990.
Kracht, 1992] M. Kracht. Even more about the lattice of tense logics. Archive of
Mathematical Logic, 31:243{357, 1992.
Kracht, 1993] M. Kracht. How completeness and correspondence theory got married.
In M. de Rijke, editor, Diamonds and Defaults, pages 175{214. Kluwer Academic
Publishers, 1993.
Kracht, 1996] M. Kracht. Tools and techniques in modal logic. Habilitationsschrift, FU
Berlin, 1996.
Kreisel and Putnam, 1957] G. Kreisel and H. Putnam. Eine Unableitbarkeitsbeweismethode fur den intuitionistischen Aussagenkalkul. Zeitschrift fur Mathematische
Logik und Grundlagen der Mathematik, 3:74{78, 1957.

ADVANCED MODAL LOGIC

175

Kruskal, 1960] J. B. Kruskal. Well-quasi-ordering, the tree theorem and Vazsonyi's
conjecture. Transactions of the American Mathematical Society, 95:210{225, 1960.
Kuznetsov and Gerchiu, 1970] A.V. Kuznetsov and V.Ya. Gerchiu. Superintuitionistic
logics and the nite approximability. Soviet Mathematics Doklady, 11:1614{1619,
1970.
Kuznetsov, 1963] A.V. Kuznetsov. Undecidability of general problems of completeness,
decidability and equivalence for propositional calculi. Algebra and Logic, 2:47{66,
1963. (Russian).
Kuznetsov, 1971] A.V. Kuznetsov. Some properties of the structure of varieties of
pseudo-Boolean algebras. In Proceedings of the XIth USSR Algebraic Colloquium,
pages 255{256, Kishinev, 1971. (Russian).
Kuznetsov, 1972] A.V. Kuznetsov. The decidability of certain superintuitionistic calculi. In Proceedings of the IInd USSR Conference on Mathematical Logic, Moscow,
1972. (Russian).
Kuznetsov, 1975] A.V. Kuznetsov. On superintuitionistic logics. In Proceedings of the
International Congress of Mathematicians, pages 243{249, Vancouver, 1975.
Kuznetsov, 1979] A.V. Kuznetsov. Tools for detecting non-derivability or nonexpressibility. In V.A. Smirnov, editor, Logical Inference. Proceedings of the USSR
Symposium on the Theory of Logical Inference, pages 5{23. Nauka, Moscow, 1979.
(Russian).
Kuznetsov, 1985] A.V. Kuznetsov. Proof-intuitionistic propositional calculus. Doklady
Academii Nauk SSSR, 283:27{30, 1985. (Russian).
Ladner, 1977] R.E. Ladner. The computational complexity of provability in systems of
modal logic. SIAM Journal on Computing, 6:467{480, 1977.
Lemmon and Scott, 1977] E.J. Lemmon and D.S. Scott. An Introduction to Modal
Logic. Oxford, Blackwell, 1977.
Lemmon, 1966a] E.J. Lemmon. Algebraic semantics for modal logic. I. Journal of
Symbolic Logic, 31:46{65, 1966.
Lemmon, 1966b] E.J. Lemmon. Algebraic semantics for modal logic. II. Journal of
Symbolic Logic, 31:191{218, 1966.
Lemmon, 1966c] E.J. Lemmon. A note on Hallden-incompleteness. Notre Dame Journal
of Formal Logic, 7:296{300, 1966.
Levin, 1969] V.A. Levin. Some syntactic theorems on the calculus of nite problems of
Yu.T. Medvedev. Soviet Mathematics Doklady, 10:288{290, 1969.
Lewis, 1918] C.I. Lewis. A Survey of Symbolic Logic. University of California Press,
Berkeley, 1918.
Lewis, 1974] D. Lewis. Intensional logics without iterative axioms. Journal of Philosophical logic, 3:457{466, 1974.
Lincoln et al., 1992] P.D. Lincoln, J. Mitchell, A. Scedrov, and N. Shankar. Decision
problems for propositional linear logic. Annals of Pure and Applied Logic, 56:239{311,
1992.
Lukasiewicz, 1952] J. Lukasiewicz. On the intuitionistic theory of deduction. Indagationes Mathematicae, 14:202{212, 1952.
Luppi, 1996] C. Luppi. On the interpolation property of some intuitionistic modal
logics. Archive for Mathematical Logic, 35:173{189, 1996.
Makinson, 1971] D.C. Makinson. Some embedding theorems for modal logic. Notre
Dame Journal of Formal Logic, 12:252{254, 1971.
Maksimova and Rybakov, 1974] L.L. Maksimova and V.V. Rybakov. Lattices of modal
logics. Algebra and Logic, 13:105{122, 1974.
Maksimova et al., 1979] L.L. Maksimova, V.B. Shehtman, and D.P. Skvortsov. The
impossibility of a nite axiomatization of Medvedev's logic of nitary problems. Soviet
Mathematics Doklady, 20:394{398, 1979.
Maksimova, 1972] L.L. Maksimova. Pretabular superintuitionistic logics. Algebra and
Logic, 11:308{314, 1972.
Maksimova, 1975a] L.L. Maksimova. Modal logics of nite slices. Algebra and Logic,
14:188{197, 1975.

176

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Maksimova, 1975b] L.L. Maksimova. Pretabular extensions of Lewis S 4. Algebra and
Logic, 14:16{33, 1975.
Maksimova, 1979] L.L. Maksimova. Interpolation theorems in modal logic and amalgamable varieties of topological Boolean algebras. Algebra and Logic, 18:348{370,
1979.
Maksimova, 1982a] L.L. Maksimova. Failure of the interpolation property in modal
companions of Dummett's logic. Algebra and Logic, 21:690{694, 1982.
Maksimova, 1982b] L.L. Maksimova. Lyndon's interpolation theorem in modal logics.
In Mathematical Logic and Algorithm Theory, pages 45{55. Institute of Mathematics,
Novosibirsk, 1982. (Russian).
Maksimova, 1984] L.L. Maksimova. On the number of maximal intermediate logics
having the disjunction property. In Proceedings of the 7th USSR Conference for
Mathematical Logic, page 95. Institute of Mathematics, Novosibirsk, 1984. (Russian).
Maksimova, 1986] L.L. Maksimova. On maximal intermediate logics with the disjunction property. Studia Logica, 45:69{75, 1986.
Maksimova, 1987] L.L. Maksimova. On the interpolation in normal modal logics. Nonclassical Logics, Studies in Mathematics, 98:40{56, 1987. (Russian).
Maksimova, 1989] L.L. Maksimova. A continuum of normal extensions of the modal
provability logic with the interpolation property. Sibirskij Matematiceskij Zurnal,
30:122{131, 1989. (Russian).
Maksimova, 1992] L.L. Maksimova. Denability and interpolation in classical modal
logics. Contemporary Mathematics, 131:583{599, 1992.
Maksimova, 1995] L.L. Maksimova. On variable separation in modal and superintuitionistic logics. Studia Logica, 55:99{112, 1995.
Mal'cev, 1970] A.I. Mal'cev. Algorithms and Recursive Functions. Wolters-Noordho,
Groningen, 1970.
Mal'cev, 1973] A.I. Mal'cev. Algebraic Systems. Springer-Verlag, Berlin-Heidelberg,
1973.
Mardaev, 1984] S.I. Mardaev. The number of prelocally tabular superintuitionistic
propositional logics. Algebra and Logic, 23:56{66, 1984.
Marx, 1995] M. Marx. Algebraic relativization and arrow logic. PhD thesis, University
of Amsterdam, 1995.
Masini, 1992] A. Masini. 2-sequent calculus: a proof theory of modality. Annals of
Pure and Applied Logic, 58:229{246, 1992.
Matiyasevich, 1967] Y.V. Matiyasevich. Simple examples of undecidable associative
calculi. Soviet Mathematics Doklady, 8:555{557, 1967.
McKay, 1968] C.G. McKay. The decidability of certain intermediate logics. Journal of
Symbolic Logic, 33:258{264, 1968.
McKay, 1971] C.G. McKay. A class of decidable intermediate propositional logics. Journal of Symbolic Logic, 36:127{128, 1971.
McKenzie, 1972] R. McKenzie. Equational bases and non-modular lattice varieties.
Transactions of the American Mathematical Society, 174:1{43, 1972.
McKinsey and Tarski, 1946] J.C.C. McKinsey and A. Tarski. On closed elements in
closure algebras. Annals of Mathematics, 47:122{162, 1946.
McKinsey and Tarski, 1948] J.C.C. McKinsey and A. Tarski. Some theorems about the
sentential calculi of Lewis and Heyting. Journal of Symbolic Logic, 13:1{15, 1948.
McKinsey, 1941] J.C.C. McKinsey. A solution of the decision problem for the Lewis
systems S 2 and S 4, with an application to topology. Journal of Symbolic Logic,
6:117{134, 1941.
Medvedev, 1962] Yu.T. Medvedev. Finite problems. Soviet Mathematics Doklady,
3:227{230, 1962.
Medvedev, 1966] Yu.T. Medvedev. Interpretation of logical formulas by means of nite
problems. Soviet Mathematics Doklady, 7:857{860, 1966.
Meyer and van der Hoek, 1995] J. Meyer and W. van der Hoek. Epistemic Logic for
AI and Computer Science. Cambridge University Press, 1995.
Mikulas, 1995] S. Mikulas. Taming Logics. PhD thesis, University of Amsterdam, 1995.

ADVANCED MODAL LOGIC

177

Minari, 1986] P. Minari. Intermediate logics with the same disjunctionless fragment as
intuitionistic logic. Studia Logica, 45:207{222, 1986.
Montagna, 1987] F. Montagna. Provability in nite subtheories of PA and relative
interpretability: a modal investigation. Journal of Symbolic Logic, 52:494{511, 1987.
Morikawa, 1989] O. Morikawa. Some modal logics based on three-valued logic. Notre
Dame Journal of Formal Logic, 30:130{137, 1989.
Muravitskij, 1981] A.Yu. Muravitskij. On nite approximability of the calculus I 4 and
non-modelability of some of its extensions. Mathematical Notes, 29:907{916, 1981.
Nagle and Thomason, 1985] M.C. Nagle and S.K. Thomason. The extensions of the
modal logic K 5. Journal of Symbolic Logic, 50:102{108, 1985.
Nishimura, 1960] I. Nishimura. On formulas of one variable in intuitionistic propositional calculus. Journal of Symbolic Logic, 25:327{331, 1960.
Ono and Nakamura, 1980] H. Ono and A. Nakamura. On the size of refutation Kripke
models for some linear modal and tense logics. Studia Logica, 39:325{333, 1980.
Ono and Suzuki, 1988] H. Ono and N. Suzuki. Relations between intuitionistic modal
logics and intermediate predicate logics. Reports on Mathematical Logic, 22:65{87,
1988.
Ono, 1972] H. Ono. Some results on the intermediate logics. Publications of the Research Institute for Mathematical Science, Kyoto University, 8:117{130, 1972.
Ono, 1977] H. Ono. On some intuitionistic modal logics. Publications of the Research
Institute for Mathematical Science, Kyoto University, 13:55{67, 1977.
Orlov, 1928] I.E. Orlov. The calculus of compatibility of propositions. Mathematics of
the USSR, Sbornik, 35:263{286, 1928. (Russian).
Ostermann, 1988] P. Ostermann. Many-valued modal propositional calculi. Zeitschrift
fur mathematische Logik und Grundlagen der Mathematik, 34:343{354, 1988.
Pigozzi, 1974] D. Pigozzi. The join of equational theories. Colloquium Mathematicum,
30:15{25, 1974.
Pitts, 1992] A.M. Pitts. On an interpretation of second order quantication in rst
order intuitionistic propositional logic. Journal of Symbolic Logic, 57:33{52, 1992.
Ponse et al., 1996] A. Ponse, M. de Rijke, and Y. Venema. Modal Logic and Process
Algebra. CSLI Publications, Stanford, 1996.
Prior, 1957] A. Prior. Time and Modality. Clarendon Press, Oxford, 1957.
Rabin, 1969] M.O. Rabin. Decidability of second order theories and automata on innite trees. Transactions of the American Mathematical Society, 141:1{35, 1969.
Rabin, 1977] M.O. Rabin. Decidable theories. In J. Barwise, editor, Handbook of Mathematical Logic, pages 595{630. Elsevier, North-Holland, 1977.
Rasiowa and Sikorski, 1963] H. Rasiowa and R. Sikorski. The Mathematics of Metamathematics. Polish Scientic Publishers, 1963.
Rautenberg, 1977] W. Rautenberg. Der Verband der normalen verzweigten Modallogiken. Mathematische Zeitschrift, 156:123{140, 1977.
Rautenberg, 1979] W. Rautenberg. Klassische und nichtklassische Aussagenlogik.
Vieweg, Braunschweig{Wiesbaden, 1979.
Rautenberg, 1980] W. Rautenberg. Splitting lattices of logics. Archiv fur Mathematische Logik, 20:155{159, 1980.
Rautenberg, 1983] W. Rautenberg. Modal tableau calculi and interpolation. Journal
of Philosophical Logic, 12:403{423, 1983.
Rieger, 1949] L. Rieger. On the lattice of Brouwerian propositional logics. Acta Universitatis Carolinae. Mathematica et Physica, 189, 1949.
Rodenburg, 1986] P.H. Rodenburg. Intuitionistic correspondence theory. PhD thesis,
University of Amsterdam, 1986.
Rose, 1953] G.F. Rose. Propositional calculus and realizability. Transactions of the
American Mathematical Society, 75:1{19, 1953.
Rybakov, 1977] V.V. Rybakov. Noncompact extensions of the logic S 4. Algebra and
Logic, 16:321{334, 1977.
Rybakov, 1978] V.V. Rybakov. Modal logics with LM-axioms. Algebra and Logic,
17:302{310, 1978.

178

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Rybakov, 1984a] V.V. Rybakov. Admissible rules for logics containing S 4:3. Siberian
Mathematical Journal, 25:795{798, 1984.
Rybakov, 1984b] V.V. Rybakov. A criterion for admissibility of rules in the modal
system S 4 and intuitionistic logic. Algebra and Logic, 23:369{384, 1984.
Rybakov, 1987] V.V. Rybakov. The decidability of admissibility of inference rules in
the modal system Grz and intuitionistic logic. Mathematics of the USSR, Izvestiya,
28:589{608, 1987.
Rybakov, 1989] V.V. Rybakov. Admissibility of inference rules in the modal system G.
Mathematical Logic and Algorithmical Problems, Mathematical Institute, Novosibirsk,
12:120{138, 1989. (Russian).
Rybakov, 1993] V.V. Rybakov. Rules of inference with parameters for intuitionistic
logic. Journal of Symbolic Logic, 58:1803{1834, 1993.
Rybakov, 1994] V.V. Rybakov. Criteria for admissibility of inference rules. Modal and
intermediate logics with the branching property. Studia Logica, 53:203{226, 1994.
Rybakov, 1995] V.V. Rybakov. Hereditarily structurally complete modal logics. Journal
of Symbolic Logic, 60:266{288, 1995.
Sahlqvist, 1975] H. Sahlqvist. Completeness and correspondence in the rst and second order semantics for modal logic. In S. Kanger, editor, Proceedings of the Third
Scandinavian Logic Symposium, pages 110{143. North-Holland, Amsterdam, 1975.
Sambin and Vaccaro, 1989] G. Sambin and V. Vaccaro. A topological proof of
Sahlqvist's theorem. Journal of Symbolic Logic, 54:992{999, 1989.
Sasaki, 1992] K. Sasaki. The disjunction property of the logics with axioms of only one
variable. Bulletin of the Section of Logic, 21:40{46, 1992.
Scroggs, 1951] S.J. Scroggs. Extensions of the Lewis system S 5. Journal of Symbolic
Logic, 16:112{120, 1951.
Segerberg, 1967] K. Segerberg. Some modal logics based on three valued logic. Theoria,
33:53{71, 1967.
Segerberg, 1970] K. Segerberg. Modal logics with linear alternative relations. Theoria,
36:301{322, 1970.
Segerberg, 1971] K. Segerberg. An essay in classical modal logic. Philosophical Studies,
Uppsala, 13, 1971.
Segerberg, 1975] K. Segerberg. That all extensions of S 4:3 are normal. In S. Kanger, editor, Proceedings of the Third Scandinavian Logic Symposium, pages 194{196. NorthHolland, Amsterdam, 1975.
Segerberg, 1986] K. Segerberg. Modal logics with functional alternative relations. Notre
Dame Journal of Formal Logic, 27:504{522, 1986.
Segerberg, 1989] K. Segerberg. Von Wright's tense logic. In P. Schilpp and L. Hahn,
editors, The Philosophy of Georg Henrik von Wright, pages 603{635. La Salle, IL:
Open Court, 1989.
Shavrukov, 1991] V.Yu. Shavrukov. On two extensions of the provability logic GL.
Mathematics of the USSR, Sbornik, 69:255{270, 1991.
Shavrukov, 1993] V.Yu. Shavrukov. Subalgebras of diagonalizable algebras of theories
containing arithmetic. Dissertationes Mathematicae (Rozprawy Matematyczne, Polska Akademia Nauk, Instytut Matematyczny), Warszawa, 323, 1993.
Shehtman, 1977] V.B. Shehtman. On incomplete propositional logics. Soviet Mathematics Doklady, 18:985{989, 1977.
Shehtman, 1978a] V.B. Shehtman. Rieger{Nishimura lattices. Soviet Mathematics
Doklady, 19:1014{1018, 1978.
Shehtman, 1978b] V.B. Shehtman. An undecidable superintuitionistic propositional
calculus. Soviet Mathematics Doklady, 19:656{660, 1978.
Shehtman, 1979] V.B. Shehtman. Kripke type semantics for propositional modal logics
with the intuitionistic base. In V.A. Smirnov, editor, Modal and Tense Logics, pages
108{112. Institute of Philosophy, USSR Academy of Sciences, 1979. (Russian).
Shehtman, 1980] V.B. Shehtman. Topological models of propositional logics. Semiotics
and Information Science, 15:74{98, 1980. (Russian).

ADVANCED MODAL LOGIC

179

Shehtman, 1982] V.B. Shehtman. Undecidable propositional calculi. In Problems of
Cybernetics. Nonclassical logics and their application, volume 75, pages 74{116. USSR
Academy of Sciences, 1982. (Russian).
Shimura, 1993] T. Shimura. Kripke completeness of some intermediate predicate logics
with the axiom of constant domain and a variant of canonical formulas. Studia Logica,
52:23{40, 1993.
Shimura, 1995] T. Shimura. On completeness of intermediate predicate logics with
respect to Kripke semantics. Bulletin of the Section of Logic, 24:41{45, 1995.
Shum, 1985] A.A. Shum. Relative varieties of algebraic systems, and propositional
calculi. Soviet Mathematics Doklady, 31:492{495, 1985.
Simpson, 1994] A.K. Simpson. The proof theory and semantics of intuitionistic modal
logic. PhD thesis, University of Edinburgh, 1994.
Smorynski, 1973] C. Smorynski. Investigations of Intuitionistic Formal Systems by
means of Kripke Frames. PhD thesis, University of Illinois, 1973.
Smorynski, 1978] C. Smorynski. Beth's theorem and self-referential sentences. In Logic
Colloquium 77, pages 253{261. North-Holland, Amsterdam, 1978.
Smorynski, 1985] C. Smorynski. Self-reference and Modal Logic. Springer Verlag, Heidelberg & New York, 1985.
Sobolev, 1977a] S.K. Sobolev. On nite-dimensional superintuitionistic logics. Mathematics of the USSR, Izvestiya, 11:909{935, 1977.
Sobolev, 1977b] S.K. Sobolev. On the nite approximability of superintuitionistic logics.
Mathematics of the USSR, Sbornik, 31:257{268, 1977.
Solovay, 1976] R. Solovay. Provability interpretations of modal logic. Israel Journal of
Mathematics, 25:287{304, 1976.
Sotirov, 1984] V.H. Sotirov. Modal theories with intuitionistic logic. In Proceedings
of the Conference on Mathematical Logic, So a, 1980, pages 139{171. Bulgarian
Academy of Sciences, 1984.
Spaan, 1993] E. Spaan. Complexity of Modal Logics. PhD thesis, Department of Mathematics and Computer Science, University of Amsterdam, 1993.
Statman, 1979] R. Statman. Intuitionistic propositional logic is polynomial-space complete. Theoretical Computer Science, 9:67{72, 1979.
Surendonk, 1996] T. Surendonk. Canonicity of intensional logics without iterative axioms. Journal of Philosophical Logic, 1996. To appear.
Suzuki, 1990] N. Suzuki. An algebraic approach to intuitionistic modal logics in connection with intermediate predicate logics. Studia Logica, 48:141{155, 1990.
Tarski, 1954] A. Tarski. Contributions to the theory of models I, II. Indagationes
Mathematicae, 16:572{588, 1954.
Thomason, 1972] S. K. Thomason. Noncompactness in propositional modal logic. Journal of Symbolic Logic, 37:716{720, 1972.
Thomason, 1974a] S. K. Thomason. An incompleteness theorem in modal logic. Theoria, 40:30{34, 1974.
Thomason, 1974b] S. K. Thomason. Reduction of tense logic to modal logic I. Journal
of Symbolic Logic, 39:549{551, 1974.
Thomason, 1975a] S. K. Thomason. The logical consequence relation of propositional
tense logic. Zeitschrift fur mathematische Logik und Grundlagen der Mathematik,
21:29{40, 1975.
Thomason, 1975b] S. K. Thomason. Reduction of second-order logic to modal logic.
Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 21:107{114,
1975.
Thomason, 1975c] S. K. Thomason. Reduction of tense logic to modal logic II. Theoria,
41:154{169, 1975.
Thomason, 1980] S. K. Thomason. Independent propositional modal logics. Studia
Logica, 39:143{144, 1980.
Thomason, 1982] S. K. Thomason. Undecidability of the completeness problem of
modal logic. In Universal Algebra and Applications, Banach Center Publications,
volume 9, pages 341{345, Warsaw, 1982. PNW{Polish Scientic Publishers.

180

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Tseitin, 1958] G.S. Tseitin. Associative calculus with unsolvable equivalence problem.
Proceedings of the Mathematical Steklov Institute of the USSR Academy of Sciences,
52:172{189, 1958. Translation: American Mathematical Society. Translations. Series
2. 94:73{92.
Tsytkin, 1978] A.I. Tsytkin. On structurally complete superintuitionistic logics. Soviet
Mathematics Doklady, 19:816{819, 1978.
Tsytkin, 1987] A.I. Tsytkin. Structurally complete superintuitionistic logics and primitive varieties of pseudo-Boolean algebras. Mathematical Studies, 98:134{151, 1987.
(Russian).
Umezawa, 1955] T. Umezawa. U ber die Zwischensysteme der Aussagenlogik. Nagoya
Mathematical Journal, 9:181{189, 1955.
Umezawa, 1959] T. Umezawa. On intermediate propositional logics. Journal of Symbolic Logic, 24:20{36, 1959.
Urquhart, 1974] A. Urquhart. Implicational formulas in intuitionistic logic. Journal of
Symbolic Logic, 39:661{664, 1974.
Urquhart, 1984] A. Urquhart. The undecidability of entailment and relevant implication. Journal of Symobolic Logic, 49:1059{1073, 1984.
Vakarelov, 1981] D. Vakarelov. Intuitionistic modal logics incompatible with the law of
excluded middle. Studia Logica, 40:103{111, 1981.
Vakarelov, 1985] D. Vakarelov. An application of the Rieger{Nishimura formulas to the
intuitionistic modal logics. Studia Logica, 44:79{85, 1985.
van Benthem and Blok, 1978] J.A.F.K. van Benthem and W.J. Blok. Transitivity follows from Dummett's axiom. Theoria, 44:117{118, 1978.
van Benthem and Humberstone, 1983] J.A.F.K. van Benthem and I.L. Humberstone.
Hallden-completeness by gluing Kripke frames. Notre Dame Journal of Formal Logic,
24:426{430, 1983.
van Benthem, 1976] J.A.F.K. van Benthem. Modal reduction principles. Journal of
Symbolic Logic, 41:301{312, 1976.
van Benthem, 1979] J.A.F.K. van Benthem. Syntactic aspects of modal incompleteness
theorems. Theoria, 45:63{77, 1979.
van Benthem, 1980] J.A.F.K. van Benthem. Some kinds of modal completeness. Studia
Logica, 39:125{141, 1980.
van Benthem, 1983] J.A.F.K. van Benthem. Modal Logic and Classical Logic. Bibliopolis, Napoli, 1983.
van der Hoek, 1992] W. van der Hoek. Modalities for Reasoning about Knowledge and
Quantities. PhD thesis, University of Amsterdam, 1992.
Venema, 1991] Y. Venema. Many-Dimensional Modal Logics. PhD thesis, Universiteit
van Amsterdam, 1991.
Visser, 1995] A. Visser. A course in bimodal provability logic. Annals of Pure and
Applied Logic, 73:115{142, 1995.
Visser, 1996] A. Visser. Uniform interpolation and layered bisimulation. In P. Hayek,
editor, Godel'96, pages 139{164. Springer Verlag, 1996.
Walukiewicz, 1993] I. Walukiewicz. A Complete Deduction system for the -calculus.
PhD thesis, Warsaw, 1993.
Walukiewicz, 1996] I. Walukiewicz. A note on the completeness of Kozen's axiomatization of the propositional -calculus. Bulletin of Symbolic Logic, 2:349{366, 1996.
Wang, 1992] X. Wang. The McKinsey axiom is not compact. Journal of Symbolic
Logic, 57:1230{1238, 1992.
Wansing, 1994] H. Wansing. Sequent calculi for normal modal propositional logics.
Journal of Logic and Computation, 4:125{142, 1994.
Wansing, 1996] H. Wansing. Proof Theory of Modal Logic. Kluwer Academic Publishers, 1996.
Whitman, 1943] P. Whitman. Splittings of a lattice. American Journal of Mathematics,
65:179{196, 1943.
Wijesekera, 1990] D. Wijesekera. Constructive modal logic I. Annals of Pure and
Applied Logic, 50:271{301, 1990.

ADVANCED MODAL LOGIC

181

Williamson, 1994] T. Williamson. Non-genuine MacIntosh logics. Journal of Philosophical Logic, 23:87{101, 1994.
Wolter and Zakharyaschev, 1997a] F. Wolter and M. Zakharyaschev. Intuitionistic
modal logics as fragments of classical bimodal logics. In E. Orlowska, editor, Logic at
Work. Kluwer Academic Publishers, 1997. In print.
Wolter and Zakharyaschev, 1997b] F. Wolter and M. Zakharyaschev. On the relation
between intuitionistic and classical modal logics. Algebra and Logic, 1997. To appear.
Wolter, 1993] F. Wolter. Lattices of Modal Logics. PhD thesis, Freie Universitat Berlin,
1993. Parts of this paper will appear in Annals of Pure and Applied Logic under the
title \The structure of lattices of subframe logics".
Wolter, 1994a] F. Wolter. Solution to a problem of Goranko and Passy. Journal of
Logic and Computation, 4:21{22, 1994.
Wolter, 1994b] F. Wolter. What is the upper part of the lattice of bimodal logics?
Studia Logica, 53:235{242, 1994.
Wolter, 1995] F. Wolter. The nite model property in tense logic. Journal of Symbolic
Logic, 60:757{774, 1995.
Wolter, 1996a] F. Wolter. Completeness and decidability of tense logics closely related
to logics containing K 4. Journal of Symbolic Logic, 1996. To appear.
Wolter, 1996b] F. Wolter. A counterexample in tense logic. Notre Dame Journal of
Formal Logic, 37:167{173, 1996.
Wolter, 1996c] F. Wolter. Properties of tense logics. Mathematical Logic Quarterly,
42:481{500, 1996.
Wolter, 1996d] F. Wolter. Tense logics without tense operators. Mathematical Logic
Quarterly, 42:145{171, 1996.
Wolter, 1997a] F. Wolter. All nitely axiomatizable subframe logics containing CSM
are decidable. Archive for Mathematical Logic, 1997. To appear.
Wolter, 1997b] F. Wolter. Fusions of modal logics revisited. In M. Kracht, M. De
Rijke, H. Wansing, and M. Zakharyaschev, editors, Advances in Modal Logic. CSLI,
Stanford, 1997.
Wolter, 1997c] F. Wolter. A note on atoms in polymodal algebras. Algebra Universalis,
1997. To appear.
Wolter, 1997d] F. Wolter. A note on the interpolation property in tense logic. Journal
of Philosophical Logic, 1997. To appear.
Wolter, 1997e] F. Wolter. Superintuitionistic companions of classical modal logics. Studia Logica, 58:229{259, 1997.
Wronski, 1973] A. Wronski. Intermediate logics and the disjunction property. Reports
on Mathematical Logic, 1:39{51, 1973.
Wronski, 1974] A. Wronski. Remarks on intermediate logics with axioms containing
only one variable. Reports on Mathematical Logic, 2:63{75, 1974.
Wronski, 1989] A. Wronski. Su#cient condition of decidability for intermediate propositional logics. In ASL Logic Colloquium, Berlin'89, 1989.
Zakharyaschev and Alekseev, 1995] M. Zakharyaschev and A. Alekseev. All nitely
axiomatizable normal extensions of K 4:3 are decidable. Mathematical Logic Quarterly,
41:15{23, 1995.
Zakharyaschev and Popov, 1979] M.V. Zakharyaschev and S.V. Popov. On the complexity of Kripke countermodels in intuitionistic propositional calculus. In Proceedings
of the 2nd Soviet{Finland Logic Colloquium, pages 32{36, 1979. (Russian).
Zakharyaschev, 1983] M.V. Zakharyaschev. On intermediate logics. Soviet Mathematics
Doklady, 27:274{277, 1983.
Zakharyaschev, 1984] M.V. Zakharyaschev. Normal modal logics containing S 4. Soviet
Mathematics Doklady, 28:252{255, 1984.
Zakharyaschev, 1987] M.V. Zakharyaschev. On the disjunction property of superintuitionistic and modal logics. Mathematical Notes, 42:901{905, 1987.
Zakharyaschev, 1988] M.V. Zakharyaschev. Syntax and semantics of modal logics containing S 4. Algebra and Logic, 27:408{428, 1988.

182

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Zakharyaschev, 1989] M.V. Zakharyaschev. Syntax and semantics of intermediate logics. Algebra and Logic, 28:262{282, 1989.
Zakharyaschev, 1991] M.V. Zakharyaschev. Modal companions of superintuitionistic
logics: syntax, semantics and preservation theorems. Mathematics of the USSR,
Sbornik, 68:277{289, 1991.
Zakharyaschev, 1992] M.V. Zakharyaschev. Canonical formulas for K 4. Part I: Basic
results. Journal of Symbolic Logic, 57:1377{1402, 1992.
Zakharyaschev, 1994] M.V. Zakharyaschev. A new solution to a problem of Hosoi and
Ono. Notre Dame Journal of Formal Logic, 35:450{457, 1994.
Zakharyaschev, 1996] M.V. Zakharyaschev. Canonical formulas for K 4. Part II: Conal
subframe logics. Journal of Symbolic Logic, 61:421{449, 1996.
Zakharyaschev, 1997a] M.V. Zakharyaschev. Canonical formulas for K 4. Part III: the
nite model property. Journal of Symbolic Logic, 62, 1997. To appear.
Zakharyaschev, 1997b] M.V. Zakharyaschev. Canonical formulas for modal and superintuitionistic logics: a short outline. In M. de Rijke, editor, Advances in Intensional
Logic, pages 191{243. Kluwer Academic Publishers, 1997.

Index
23
L -formula, 44

compactness, 31
complete set of formulas, 8
complex variety, 34
complexity function, 161
conguration problem, 146
congruential logic, 166
conservative formula, 76
cover, 13
cycle free frame, 17, 81

L

{prime logic, 8
-irreducible logic, 8
{-complex logic, 34
{-generated frame, 11, 81
n-transitive logic, 6, 81
actual world, 60
actual world condition, 61
amalgamability, 73
atom, 13, 18
axiomatic basis, 8
axiomatization
nite, 7
independent, 7
problem, 15
recursive, 7

d-cyclic set, 13
deduction theorem, 5
deductively equivalent formulas, 5
degree of incompleteness, 27
depth of a frame, 12
descriptive frame, 11, 81
di erence operator, 167
di erentiated frame, 11, 81
disjunction property, 129
modal, 129
distinguished point, 60
downward directness, 24
Dummett logic, 117

Beth property, 69
bimodal companion, 142
bisimulation, 167
canonical formula, 39
intuitionistic, 117
quasi-normal, 62
canonicity, 19
CDC, 37
closed domain, 37
closed domain condition, 37
cluster assignment, 97
conal subframe formula, 45
conal subframe logic, 45
quasi-normal, 63
compact frame, 11

elementary logic, 26
essentially negative formula, 127
nite embedding property, 48
nite model property
exponential, 161
global, 32
polynomial, 161
xed point operator, 167
focus, 52
183

184

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

frame formula, 39
fusion, 83
Godel translation, 113
global derivability, 5
global Kripke completeness, 32
graded modality, 167
Hallden completeness, 77
Heyting algebra, 111
inaccessible world, 80
independent set of formulas, 8
inference rule
admissible, 149
derivable, 149
interpolant, 69
post-, 77
interpolation property, 69
for a consequence relation, 70
intersection of logics, 6
intuitionistic frame, 112
intuitionistic modal frame, 138
intuitionistic modal logic, 136
Jankov formula, 39
Kreisel{Putnam logic, 130
Kripke frame, 9
Lob axiom, 35
linear tense logic, 98
local tabularity, 42
logic of a class of frames, 9
Medvedev's logic, 134
minimal tense extension, 93
Minsky machine, 146
modal companion, 119
modal degree, 20
modal matrix, 60
negative formula, 21
Nishimura formula, 113

Noetherian frame, 35
nominal, 167
non-eliminability, 20
non-iterative logic, 82
normal lter, 73
normal form, 42
open domain, 37, 115
p-morphism, 11
persistence, 19
polymodal frame, 81
polymodal logic, 80
polynomially equivalent logics, 161
positive formula, 21
pretabularity, 67
prime lter, 112
prime formula, 8
pseudo-Boolean algebra, 111
quasi-normal logic, 59
reduced frame, 20
reduction, 11, 81
weak, 106
rened frame, 11
rened rened, 81
replacement function, 95
Rieger{Nishimura lattice, 112
root, 9, 81
rooted frame, 9
Sahlqvist formula, 26, 82
Scott logic, 130
semantical consequence, 160
si-fragment, 119
si-logic, 111
simulation of a frame, 90
simulation of a logic, 90
skeleton, 113
skeleton lemma, 114
Smetanich logic, 117
splitting, 15

ADVANCED MODAL LOGIC

union-, 15
splitting pair, 8
standard translation, 55
strict Kripke completeness, 15
strict sf-completeness, 48
strong global completeness, 32
strong Kripke completeness, 31
strongly positive formula, 22
structural completeness, 151
subframe, 35, 36, 65, 81, 115
conal, 46, 65
generated, 9, 81
subframe formula, 45
subframe logic, 45, 46
quasi-normal, 63
subreduction, 36
conal, 36
quasi-, 61
weak, 107
sum of logics, 6
superamalgamability, 73
superintuitionistic logic, 111
surrogate, 84
surrogate frame, 106
t-line logic, 102
tabularity, 65
Tarski's criterion, 7
tense frame, 93
tense logic, 93
tight frame, 11
time-line, 102
topological Boolean algebra, 113
undecidable formula, 149
uniform formula, 43
uniform interpolation, 77
universal frame of rank n, 12
universal modality, 87
untied formula, 25
upward closed set, 9
weak Kreisel{Putnam formula, 116

185

