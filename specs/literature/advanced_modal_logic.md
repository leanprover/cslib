Preface

.

i

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

ADVANCED MODAL LOGIC

This chapter is a continuation of the preceding one. and we begin it at the

place where the authors of

left us about fifteen years

Basic Modal Logic

ago. Concluding his historical overview. Krister Segerberg wrote: "Where

we stand today is difficult to say.

Is the picture beginning to break up.

or is it just the contemporary observer's perennial problem of putting his

own time into perspective?" So. where did modal logic of the 1980s stand?

Where does it stand now? Modal logicians working in philosophy. computer

science. artificial intelligence. linguistics or some other fields would probably

give different answers to these questions. Our interpretation of the history

of modal logic and view on its future is based upon understanding it as part

of mathematical logic.

Modal logicians of the First Wave constructed and studied modal systems

trying to formalize a few kinds of necessity-like and possibility-like opera-

tors. The industrialization of the Second Wave began with the discovery

of a deep connection between modal logics on the one hand and relational

and algebraic structures on the other. which opened the door for creating

many new systems of both artificial and natural origin. Other disciplines—

the foundations of mathematics. computer science. artificial intelligence.

etc.—brought (or rediscovered

) more. "This framework has had enormous

.

influence. not only just on the logic of necessity and possibility. but in other

areas as well. In particular. the ideas in this approach have been applied

to develop formalisms for describing many other kinds of structures and

processes in computer science. giving the sub ject applications that would

have probably surprised the sub ject's founders and early detractors alike"

[Barwise and Moss 1996]. Even two or three mathematical ob jects may lead

to useful generalizations. It is no wonder then that this huge family of logics

gave rise to an abstract notion (or rather notions) of a modal logic. which

in turn put forward the problem of developing a general theory for it.

Big classes of modal systems were considered already in the 1970s. say

extensions of

[Scroggs 1971] or

[Dummett and Lemmon 1979]. Com-

S.

S,

pleteness theorems of Lemmon and Scott [1988].

Bull [1966b] and Segerberg

,

[1981] demonstrated that many logics. formerly investigated "piecewise".

.

One of the celebrities in modal logic.the Gfiodel.Lfiob provability logic

.was :rst

GL

introduced by Segerberg "5'?5" as an 1arti:cial9 system under the name

8

K.W

,

This book was written in 5'008

ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

have in fact very much in common and can be treated by the same meth-

ods. A need for a uniting theory became obvious. "There are two main

lacunae in recent work on modal logic: a lack of general results and a lack

of negative results. This or that logic is shown to have such and such a prop-

erty. but very little is known about the scope or bounds of the property.

Thus there are numerous results on completeness. decidability. finite model

property. compactness. etc. but very few general or negative results". wrote

Fine [1985c]. The creation of duality theory between relational and algebraic

semantics ([Lemmon 1966a.b]. [Goldblatt 1986a.b]). originated actually by

Joonsson and Tarski [1971]. the establishment of the connection between

modal logics and varieties of modal algebras ([Kuznetsov 1981]. Maksimova

and Rybakov [1985]. [Blok 1986]). and between modal and first and higher

order languages ([Fine 1987b]. [van Benthem 1962]) added those mathemat-

ical ingredients that were necessary to distinguish modal logic as a separate

branch of mathematical logic.

On the other hand. various particular systems became sub jects of more

special disciplines. like provability logic. deontic logic. tense logic. etc. which

has found reflection in the corresponding chapters of this Handbook.

In the 1960s and 1990s modal logic was developing both "in width"

and "in depth". which made it more difficult for us to select material for

this chapter. The expansion "in width" has brought in sight new interest-

ing types of modal operators. thus demonstrating again the great expres-

sive power of propositional modal languages. They include. for instance.

polyadic operators. graded modalities. the fixed point and difference op-

erators. We hope the corresponding systems will be considered in detail

elsewhere in the Handbook4 in this chapter they are briefly discussed in the

appendix. where the reader can find enough references.

Instead of trying to cover the whole variety of existing types of modal

operators. we decided to restrict attention mainly to the classes of normal

(and quasi-normal) uni- and polymodal logics and follow "in depth" the

way taken by Bull and Segerberg in

. the more so that

Basic Modal Logic

this corresponds to our own scientific interests.

Having gone over from considering individual modal systems to big classes

of them. we are certainly interested in developing general methods suitable

for handling modal logics

. This somewhat changes the standard

en masse

set of tools for dealing with logics and gives rise to new directions of research.

First. we are almost completely deprived of proof-theoretic methods like

Gentzen-style systems or natural deduction. Although proof theory has

been developed for a number of important modal logics. it can hardly be

extended to reasonably representative families. (Proof theory is discussed

in the chapter

4 some references to recent

Sequent systems for modal logics

results can be found in the appendix.)

ADVANCED MODAL LOGIC

—

In fact. modern modal logic is primarily based upon the frame-theoretic

and algebraic approaches. The link connecting syntactical representations

of logics and their semantics is general completeness theory which stems

from the pioneering results of Bull [1966b]. Fine [1985c]. Sahlqvist [1987].

Goldblatt and Thomason [1985]. Completeness theorems are usually the

first step in understanding various properties of logics. especially those that

have semantic or algebraic equivalents. A classical example is Maksimova's

[1989] investigation of the interpolation property of normal modal logics

containing

. or decidability results based on completeness with respect to

S,

"good" classes of frames. Completeness theory provides means for axiom-

atizing logics determined by given frame classes and characterizes those of

them that are modal axiomatic.

Standard families of modal logics are endowed with the lattice structure

induced by the set-theoretic inclusion. This gives rise to another line of

studies in modal logic. addressing questions like "what are co-atoms in the

lattice?" (i.e. what are maximal consistent logics in the family?). "are there

infinite ascending chains?" (i.e. are all logics in the family finitely axioma-

tizable?). etc. From the algebraic standpoint a lattice of logics corresponds

to a lattice of subvarieties of some fixed variety of modal algebras. which

opens a way for a fruitful interface with a well-developed field in universal

algebra.

A striking connection between "geometrical" properties of modal formu-

las. completeness. axiomatizability and

-prime elements in the lattice of

modal logics was discovered by Jankov [1962. 1969]. Blok [1986. 1960b]

T

and Rautenberg [1989]. These observations gave an impetus to a pro ject

of constructing frame-theoretic languages which are able to characterize

the "geometry" and "topology" of frames for modal logics ([Zakharyaschev

1965. 1993]. [Wolter 1996d]) and thereby provide new tools for proving their

properties and clarifying the structure of their lattices.

One more interesting direction of studies. arising only when we deal with

big classes of logics. concerns the algorithmic problem of recognizing prop-

erties of (finitely axiomatizable) logics. Having undecidable finitely axiom-

atizable logics in a given class ([Thomason 1987a]. [Shehtman 1986b]). it

is tempting to conjecture that non-trivial properties of logics in this class

are undecidable. However. unlike Rice's Theorem in recursion theory. some

important properties turn out to be decidable. witness the decidability of

interpolation above

([Maksimova 1989]). The machinery for proving the

S,

undecidability of various properties (e.g. Kripke completeness and decid-

ability) was developed in [Thomason 1963] and [Chagrov 1990b.c].

Thomason [1963] proved the undecidability of Kripke completeness first

in the class of polymodal logics and then transferred it to that of unimodal

ones. In fact. Thomason's embedding turns out to be an isomorphism from

(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

the lattice of logics with n necessity operators onto an interval in the lat-

tice of unimodal logics. preserving many standard properties ([Kracht and

Wolter 1998a]). Such embeddings are interesting not only from the theoret-

ical point of view but can also serve as a vehicle for reducing the study of

one class of logics to another. Perhaps the best known example of such a

reduction is the G;odel translation of intuitionistic logic and its extensions

into normal modal logics above

([Maksimova and Rybakov 1985]. [Blok

S,

1986]. [Esakia 1989a.b]). We will take advantage of this translation to give

a brief survey of results in the field of superintuitionistic logics which actu-

ally were always studied in parallel with modal logics (see also Section 7 in

Intuitionistic Logic

).

Listed above are the most important general directions in mathemati-

cal modal logic we are going to concentrate on in this chapter. They. of

course. do not cover the whole discipline. Other topics. for instance. modal

systems with quantifiers. the relationship between the propositional modal

language and the first (or higher) order classical language. or proof theory

are considered in other chapters of the Handbook.

It should be emphasized once again that the reader will find no discus-

sions of particular modal systems in this chapter. Modal logic is presented

here as a mathematical theory analyzing big families of logics and thereby

providing us with powerful methods for handling concrete ones. (In some

cases we illustrate technically complex methods by considering concrete log-

ics4 for instance Rybakov's [1995] technique of proving the decidability of

the admissibility problem for inference rules is explained only for

.)

GL

Acknowledgments.

First of all. we are indebted to our friend and col-

league Marcus Kracht who not only helped us with numerous advices but

also supplied us with some material for this chapter. We are grateful to

Hiroakira Ono and the members of his Logic Group in Japan Advanced

Institute of Science and Technology for the creative and stimulating atmo-

sphere that surrounded the first two authors during their stay in JAIST.

where the bulk of the chapter was written. Thanks are also due to Johan

van Benthem. Wim Blok. Dov Gabbay. Silvio Ghilardi. Krister Segerberg.

Heinrich Wansing for their helpful comments and stimulating discussions.

And certainly our work would be impossible without constant support and

love of our wives: Olga. Imke and Lilia.

Partly the work of the first author was ,nanced by the Alexander von

Humboldt Foundation.

ADVANCED MODAL LOGIC

)

1 UNIMODAL LOGICS

We begin by considering normal modal logics with one necessity operator.

which were introduced in Section 6 of

. Recall that each

Basic Modal Logic

such logic is a set of modal formulas (in the language with the primitive

connectives

.

.

.

.

) containing all classical tautologies. the modal

.

axiom

(p

q)

(

p

q). and closed under substitution. modus

.

.

.

.

,

.

:

ponens and necessitation .,

.

.

.

.

.

.,. The lattice

NExt

K

First let us have a look at the class of normal modal logics from a purely

syntactic point of view. Given a normal modal logic L

. we denote by

.

NExtL

the family of its

ormal

xtensions. NExt

is thus the class of all

n

e

K

.

normal modal logics. Each logic L in NExtL

can be obtained by adding

.

to L

a set of modal formulas Φ and taking the closure under the inference

.

rules mentioned above4 in symbols this is denoted by

L ⊆ L

Φ.

.

"

Formulas in Φ are called

(or

)

L

L

. Formulas

additional

extra

axioms of

over

.

. and : are said to be

in NExtL

if L

. ⊆ L

: .

deductively equivalent

.

.

.

For instance.

p

p and p

p are deductively equivalent in NExt

.

K

.

,

"

"

both axiomatizing

. however (

p

p)

(p

p)

. (For more in-

T

K

.

.

.

,

formation on the relation between these formulas see [Chellas and Segerberg

.

5

.

'?

1995] and [Williamson 1995].)

We distinguish between two kinds of derivations from assumptions in a

logic L

NExt

. For a formula . and a set of formulas Φ. we write Φ

.

L

K

if there is a derivation of . from formulas in L and Φ with the help of only

?

"

modus ponens. In this case the standard deduction theorem—Φ" :

. iff

L

"

Φ

:

.—holds. The fact of derivability of . from Φ in L using both

L

"

.

modus ponens and necessitation is denoted by Φ

.4 in such a case we

.

L

say that . is

from Φ in L. For this kind of derivation

global ly derivable

:

"

we have the following variant of the deduction theorem which is proved by

induction on the length of derivations in the same manner as for classical

logic.

THEOREM 1.1 (Deduction)

L

NExt

.

For every logic

. al l formulas

K

and

. and al l sets of formulas

:

Φ

.

?

m

.

Φ" :

.

.

i,

m

0 Φ

.

,

:

."

L

L

"

1

9

"

.

where

and

is

pre.xed by

: ⊆

:

. . .

:

:

:

n

boxes:

,

m

m

n

.

.

.

.

.

.

.

.

.

.

This name is motivated by the semantical characterization of

to be given in

L

Theorem 585'8

0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

It is to be noted that in general no upper bound for m can be computed

even for a decidable L (see Theorem 5.3). However. if the formula

tra

n

⊆

,

p

p

.

.

n

n

".

.

is in L—such L is called n-

—then we can clearly take m ⊆ n. In

transitive

particular. for every L

NExt

. Φ" :

. iff Φ

:

. where

K,

.

.

L

L

"

.

"

.

.

?

"

"

.

: ⊆ :

: . Moreover. a sort of conversion of this observation holds.

.

THEOREM 1.3

L

The fol lowing conditions are equivalent for every logic

in

NExt

K

"

(i) L

n

is

5transitive. for some

n 5 '

'

(ii)

?(p" q)

.

:

there exists a formula

such that. for any

.

and

Φ

.

Φ" :

.

.

Φ

.

?(: " .).

i,

L

L

"

"

Proof

The implication (i)

(ii) is clear. To prove the converse. observe

first that ?(p" q)

?(p" q) and so ?(p" q)" p

q . By Theorem 1.1. we

.

L

.

L

8

then have ?(p" q)

p

q . for some n. Let q ⊆

p. Then

.

,

L

"

n

"

n

".

.

.

n

".

"

n

n

.

".

n

n

".

".

.

.

.

.

.

?(p"

p)

p

p. And since p

p. ?(p"

p)

L.

.

,

L

.

L

Consequently.

L.

n

tra

.

"

.

"

?

?

Remark

. Note also that (i) is equivalent to the algebraic condition: the

variety of modal algebras for L has equationally definable principal congru-

ences. For more information on this and close results consult [Blok and

Pigozzi 1963].

The

L

L

and

L

L

of logics L

" L

NExtL

are

sum

intersection

.

,

.

,

.

,

.

clearly logics in NExtL

as well. The former can be axiomatized simply by

.

"

0

?

joining the axioms of L

and L

. To axiomatize the latter we require the

.

,

following definition. Given two formulas .(p

" . . . " p

) and :(p

" . . . " p

)

.

.

n

m

(whose variables are in the lists p

" . . . " p

and p

" . . . " p

. respectively).

.

.

n

m

denote by .

: the formula .(p

" . . . " p

)

:(p

" . . . " p

).

.

".

"

n

n

n

m

,

,

THEOREM 1.2

L

⊆ L

.

: i

I

L

⊆ L

:

: j

J

Let

and

:

.

.

,

.

i

j

Then

" f

?

g

" f

?

g

L

L

⊆ L

.

:

: i

I " j

J" m" n

0

.

.

,

.

i

j

m

n

.

.

0

" f

,

?

?

9

g

Proof

Denote by L the logic in the right-hand side of the equality to be

established and suppose that ?

L

L

. Then for some m" n

0 and some

.

,

finite I

and J

such that all .

and :

. for i

I

. j

J

. are substitution

.

.

.

i

.

j

.

.

?

0

9

instances of some .

and :

. for i

I . j

J . we have

i

j

.

.

.

.

?

?

?

?

m

n

.

.

,

.

.

?

L

"

,

:

.

?

L

"

i

j

.

.

.

.

.

?

.

?

i

I

.

j

J

.

:

:

ADVANCED MODAL LOGIC

?

from which

k

l

.

.

(

.

: .

)

?

L

i

j

.

,

.

?

.

.

i

I

.j

J

,

,

.

.

.

.

,

k.l

m

n

and so ?

L because

.

:

is a substitution instance of

.

:

.

.

i

.

j

i

j

.

.

.

.

.

.

k

l

k

l

?

,

,

Thus. L

L

L. The converse inclusion is obvious.

.

,

.

0

ff

Although the sum of logics differs in general from their union. these two

operations have a few common important properties.

THEOREM 1.5

The operation

is idempotent. commutative. associative

and distributes over

' the operation

distributes over ?in.nite" sums. i:e:.

"

0

0

L

L

⊆

(L

L

).

i

i

0

0

i

I

i

I

M

M

:

:

It follows that

NExtL

"

"

is a complete distributive lattice. with L

.

.

and the inconsistent logic. i.e. the set

of all modal formulas. being its

For

h

"

0i

zero and unit elements. respectively. and the set-theoretic

its correspond-

ing lattice order. Note. however. that

does not in general distribute over

ff

infinite intersections of logics. For otherwise we would have

"

(

)

(

) ⊆

(

)"

K

K

K

.

.

.

.

n

n

" -

:

"

"

:

" -

: "

:

.

,

.

,

n.,

n.,

,

,

which is a contradiction. since the logic in the left-hand side is consistent

(

. to be more precise). while that in the right-hand side is not.

D

If we are interested in finding a simple (in one sense or another) syntactic

representation of a logic L

NExtL

. we can distinguish

.

.nite

recursive

.

and

L

L

. The former two notions

independent axiomatizations of

over

.

?

mean that L ⊆ L

Φ. for some finite or. respectively. recursive Φ. and

.

"

a set of axioms Φ is independent over L

if L

⊆ L

  for any proper

.

.

subset   of Φ. In the case when L

is

or any other finitely axiomatizable

K

.

"

over

logic. we may omit mentioning L

and say simply that L is finitely

K

.

(recursively. independently) axiomatizable.

It is fairly easy to see that L is not finitely axiomatizable over L

iff

.

there is an infinite sequence of logics L

L

. . . in NExtL

such that

.

,

.

L ⊆

L

. This observation is known as

. (It is worth

Tarski1s criterion

i.

.

i

—

—

noting that finite axiomatizability is not preserved under

. For example.

L

using Tarski's criterion. one can show that

(

p

p) is not

D

K

0

.

.

finitely axiomatizable.) The recursive axiomatizability of a logic L. as was

0

"

,

-

observed by Craig [1972]. is equivalent to the recursive enumerability of L.

As for independent axiomatizability. an interesting necessary condition can

be derived from [Kleyman 1965]. Suppose a normal modal logic L

has an

.

'
fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

independent axiomatization. Then. for every finitely axiomatizable normal

modal logic L

L

. the interval of logics

,

.

—

[L

" L

] ⊆

L

NExt

: L

L

L

K

,

.

,

.

f

?

ff

ff

g

contains an immediate predecessor of L

. Using this condition Chagrov and

.

Zakharyaschev [1997a] constructed various logics in NExt

. NExt

and

K,

S,

NExt

without independent axiomatizations.

Grz

To understand the structure of the lattice NExtL

it may be useful to

.

look for a set Φ of formulas which is

in the sense that its formulas

complete

are able to axiomatize all logics in the class. and

in the sense

independent

that it contains no complete proper subsets. Such a set (if it exists) may be

called an

of NExtL

. The existence of an axiomatic basis

axiomatic basis

.

depends on whether every logic in the class can be represented as the sum

of "indecomposable" logics. A logic L

NExtL

is said to be

!

irreducible

.

in NExtL

if for any family

L

: i

I

of logics in NExtL

. L ⊆

L

i

i

.

.

L

i

I

?

implies L ⊆ L

for some i

I . L is

!

if for any family

L

: i

I

.

prime

i

i

L

f

?

g

:

L

L

only if there is i

I such that L

L

.

It is not hard to

i

i

i

I

L

?

f

?

g

ff

:

?

ff

see (using Theorem 1.5) that a logic is

!irreducible iff it is

!prime.

L

This does not hold. however. for the dual notions of

!irreducible and

!

L

L

prime logics. We have only one implication in general: if L is

!prime (i.e.

T

T

i

I

T

L

L only if L

L. for some i

I ) then it is

!irreducible (i.e.

i

i

:

ff

ff

?

L ⊆

L

only if L ⊆ L

. for some i

I ). A formula . is said to be

i

i

T

i

I

T

prime

in NExtL

if L

. is

!prime in NExtL

.

.

.

.

T

:

?

PROPOSITION 1.7

Suppose a set of formulas

is complete for

Φ

NExtL

.

"

L

and contains no distinct deductively equivalent in

formulas: Then

NExtL

.

Φ

NExtL

Φ

is an axiomatic basis for

i, every formula in

is prime:

.

Although the definitions above seem to be quite simple. in practice it

is not so easy to understand whether a given logic is

! or

!prime. at

least at the syntactical level. However. these notions turn out to be closely

L

T

related to the following lattice-theoretic concept of splitting for which in the

next section we shall provide a semantic characterization.

A pair (L

" L

) of logics in NExtL

is called a

in NExtL

splitting pair

.

,

.

.

if it divides the lattice NExtL

into two disjoint parts: the filter NExtL

.

,

and the ideal [L

" L

]. In this case we also say that L

and L

splits

cosplits

.

.

.

,

NExtL

.

.

THEOREM 1.6

L

NExtL

NExtL

A logic

splits

i, it is

9prime in

. and

.

.

.

L

NExtL

NExtL

cosplits

i, it is

9prime in

: Moreover. the fol lowing

,

.

.

T

conditions are equivalent"

L

(i) (L

" L

)

NExtL

is a splitting pair in

'

.

,

.

(ii) L

NExtL

L

⊆

L

NExtL

: L

L

is

9prime in

and

'

.

.

,

.

.

(iii) L

NExtL

L

⊆

L

NExtL

: L

L

is

9prime in

and

:

,

.

.

.

,

T

T

f

?

'ff

g

L

L

f

?

'(

g

ADVANCED MODAL LOGIC

'

Splittings were first introduced in lattice theory by Whitman [1952] and

McKenzie [1983] (see also [Day 1988]. [Jipsen and Rose 1992]). Jankov

[1962. 1966b. 1969]. Blok [1986] and Rautenberg [1988] started using split-

tings in non-classical logic.

A few standard normal modal logics are listed in Table 1. Note that

our notations are somewhat different from those used in

Basic Modal logic

.

A

(

was introduced by Artemov4 see [Shavrukov 1991]. The formulas B

.

n

bounding depth of frames are defined in Section 17 of

.)

Basic Modal Logic

.,. Semantics

The algebraic counterpart of a logic L

NExt

is the variety of modal

K

algebras validating L (for definitions consult Section 10 of

Basic Modal

?

Logic

). Conversely. each variety (equationally definable class)

of modal

algebras determines the normal modal logic Log

⊆

. :

⊆ .

.

V

A

A

Thus we arrive at a dual isomorphism between the lattice NExt

and the

K

V

f

)

? V

j

g

lattice of varieties of modal algebras. which makes it possible to exploit the

apparatus of universal algebra for studying modal logics.

It is often more convenient. however. to deal not with modal algebras

directly but with their relational representations discovered by Joonsson and

Tarski [1971] and now known as general frames. Each

⊆

general frame

F

W" R" P

is a hybrid of the usual Kripke frame

W" R

and the modal algebra

h

i

h

i

"

F

⊆

P"

" W"

"

"

"

"

in which the operations

and

are uniquely

.

,

.

,

h

fl

[

0

6

i

W

determined by the accessibility relation R: for every X

P

3

.

?

ff

.

,

.

X ⊆

x

W :

y (xRy

y

X )

"

X ⊆

X.

f

?

)

.

?

g

[

[

So. using general frames we can take advantage of both relational and alge-

braic semantics. To simplify notation. we denote general frames of the form

F

F

⊆

W" R" 3

by

⊆

W" R

. Such frames will be called

Kripke frames

.

W

Given a class of frames

. we write Log

to denote the logic determined by

.

:

h

i

. i.e. the set of formulas that are valid in all frames in

4 it is called the

C

C

C

C

logic of

. If

consists of a single frame

. we write simply Log

.

F

F

C

C

Basic facts about duality between frames and algebras can be found in the

chapters

and

. Here we remind

Basic Modal Logic

Correspondence Theory

the reader of the definitions that will be important in what follows.

A frame

⊆

V " S" Q

is said to be a

of a frame

generated subframe

G

F

F

⊆

W" R" P

if V

W is

in

. i.e. x

V and xRy imply

upward closed

h

i

h

i

ff

?

y

V . S ⊆ R

V and Q ⊆

X

V : X

P

. The smallest generated

.

?

f

0

?

g

subframe

of

containing a set X

W is called the

subframe generated

G

F

by

rooted

root

X . A frame

is

if there is x

W —a

of

—such that the

F

F

ff

subframe of

generated by

x

is

itself.

F

F

?

f

g

5[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

D

K

⊆

p

p

.

,

T

K

⊆

p

p

.

"

.

KB

K

⊆

p

p

.,

"

.

K,

K

⊆

p

p

.

.

"

.

K.

K

⊆

p

p

,.

.

"

.

"

.

Alt

K

n

n

n

⊆

p

(p

p

)

. . .

(p

. . .

p

p

)

.

.

,

.

".

.

.

.

"

,

.

,

,

.

.

.

D,

K,

⊆

,

S,

K,

⊆

p

p

"

]

.

"

.

GL

K,

⊆

(

p

p)

p

.

.

.

Grz

K

⊆

(

(p

p)

p)

p

.

.

.

"

.

.

"

.

.

.

K,

:

K,

.

⊆

p

p

.,

,.

"

.

K,

"

K,

.

⊆

(p

q)

(p

q)

,

.

.

,

K,

5

K,

.

⊆

(

p

q)

(

q

p)

"

.

.

,

.

.

.

.

"

"

"

.

,

.

S,

:

S,

.

⊆

p

p

.,

,.

S,

"

S,

.

⊆

p

p

,.

.,

"

.

"

.

S,

5

S,

.

⊆

(

p

q)

(

q

p)

.

.

.

.

"

.

,

.

Triv

K,

⊆

p

p

.

Verum

K,

⊆

p

.

"

5

S.

S,

⊆

p

p

.,

"

KfiB

K,

⊆

p

p

.,

"

.

A

GL

⊆

p

(

p

q)

(

q

p)

.

"

.

.

.

.

.

.

"

"

Dum

S,

⊆

(

(p

p)

p)

(

p

p)

.

.

.

,.

"

.

.

,

.

KfiBW

K,

n

⊆

p

i

(p

(p

p

))

i

j

j

,

,

,

i

5.

.

5

i

j

n

"

.

,

,

.

,

"

.

.

.

.

n

KfiBD

K,

n

⊆

B

n

V

W

K,

K,

n:m

⊆

p

p" for 1

m 5 n

"

n

m

.

.

"

.

7

Table 1. A list of standard normal modal logics.

"
ADVANCED MODAL LOGIC

55

A map f from W onto V is a

(or

) of a frame

reduction

pffimorphism

F

G

⊆

W" R" P

to

⊆

V " S" Q

if the following three conditions are satisfied

h

i

h

i

for all x" y

W and X

Q

?

?

(R1)

xRy implies f (x)S f (y)4

(R3)

f (x)S f (y) implies

z

W (xRz

f (z ) ⊆ f (y))4

(R2)

f

(X )

P .

5

.

?

1

?

.

The operations of reduction and generating subframes are relational coun-

terparts of the algebraic operations of forming subalgebras and homomor-

phic images. respectively. and so preserve validity.

A frame

⊆

W" R" P

is

if. for any x" y

W .

difierentiated

F

h

i

?

x ⊆ y iff

X

P (x

X

y

X ).

)

?

?

5

?

F

is

if

tight

xRy iff

X

P (x

X

y

X ).

.

)

?

?

.

?

Those frames that are both differentiated and tight are called

. A

re.ned

frame

is said to be

if every subset

of P with the finite in-

compact

F

tersection property (i.e. with

⊆

for any finite subset

of

) has

.

.

X

non-empty intersection. Finally. refined and compact frames are called

de5

T

X

fl

X

X

scriptive

. A characteristic property of a descriptive

is that it is isomorphic

F

to its bidual (

)

. The classes of all differentiated. tight. refined and de-

"

"

F

scriptive frames will be denoted by

.

.

and

. respectively.

When representing frames in the form of diagrams. we denote by

ir-

DF

T

R

D

reflexive points. by

reflexive ones. and by

two-point clusters. An arrow

5

o

.

.

o o

from x to y means that y is accessible from x. If the accessibility relation

,

:

is transitive. we draw arrows only to the immediate successors of x.

EXAMPLE 1.8 (Van Benthem 1989) Let

⊆

W" R" P

be the frame whose

F

underlying Kripke frame is shown in Fig. 1 (' " 1 sees only ' and the

h

i

subframe generated by ' is transitive) and X

W is in P iff either X is

finite and ' ,

X or X is cofinite in W and '

X . It is easy to see that

ff

P is closed under

.

and

. Clearly.

is refined. Suppose

is a subset

?

?

,

F

of P with the finite intersection property. If

contains a finite set then

0

[

X

obviously

⊆

. And if

consists of only infinite sets then '

.

X

Thus.

is descriptive.

F

T

T

X '

fl

X

?

X

A frame

is said to be

-

.

a cardinal. if its dual

is

.

.

generated

F

F

"

a

-generated algebra.

Each modal logic L is determined by the free

.

'

finitely generated algebras in the corresponding variety. i.e. by the Tarski!

Lindenbaum (or canonical) algebras

(n) for L in the language with n 5

L

A

:

An algebra is said to be

.generated if it contains a set

of cardinality

such

.

X

,

.

that the closure of

under the algebra6s operations coincides with its universe8

X

'
5ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

nontransitive

transitive

' " 1 '

3

1

0

.

. .

5

o

6 6 6

5

5

5

Figure 1.

' variables. Their duals are denoted by

(n) ⊆

W

(n)" R

(n)" P

(n)

L

L

L

L

F

and called the

n

L. Analogous notation and

universal frames of rank

for

h

i

terminology will be used for the free algebras

(

) with

generators.

L

A

.

.

Note that

W

(

)" R

(

)

is (isomorphic to) the canonical Kripke frame

L

L

.

.

for L with

variables (defined in Section 11 of

Basic Modal Logic

) and

.

h

i

P

(

) is the collection of the truth-sets of formulas in the corresponding

L

.

canonical model. Unless otherwise stated. we will assume in what follows

that the language of the logics under consideration contains ' variables.

An important property of the universal frame of rank

for L is that

.

every descriptive

-generated frame for L.

. is a generated subframe

.

.

.

.

.

of

(

). Thus. the more information about universal frames for L we have.

L

F

.

7

the deeper our knowledge about the structure of arbitrary frames for L and

thereby about L itself.

Although in general universal frames for modal logics are very compli-

cated. considerable progress was made in clarifying the structure of the

upper part (points of finite depth) of the universal frames of finite rank

for logics in NExt

. The studies in this direction were started actually

K,

by Segerberg [1981]. Shehtman [1986a] presented a general method of con-

structing the universal frames of finite rank for logics in NExt

with the

S,

finite model property. Later similar results were obtained by other authors4

see e.g. [Bellissima 1967]. The structure of free finitely generated algebras

for

was investigated by Blok [1986].

S,

Let us try to understand first the constitution of an arbitrary transitive

refined frame

⊆

W" R" P

with n generators G

" . . . " G

P . Define

.

n

F

V

to be the valuation of the set of variables # ⊆

p

" . . . " p

in

such that

.

n

F

h

i

?

x

⊆ p

iff x

G

. Say that points x and y are #-

. x

y in

equivalent

i

i

?

f

g

j

?

2

symbols. if the same variables in # are true at them4 for X" Y

W we

write X

Y if every point in X is #-equivalent to some point in Y and

?

ff

vice versa. Let d(

) denote the

of

4 if

is of infinite depth. we

depth

F

F

F

2

"

write d(

) ⊆

. For d 5 d(

). W

and W

are the sets of all points in

F

F

F

5

d

.d

of depth d and " d. respectively4 W

. W

. etc. are defined analogously.

,

4

.d

d

d

d

F

F

,

,

is the subframe of

generated by W

. The set of all successors

(predecessors) of points in a set X

W is denoted by X

(respectively.

"

In Section 5) of Basic Modal Logic

]

7 was called the rank of

8

d

F

F

ff

3

ADVANCED MODAL LOGIC

5—

X

)4 in the transitive case X

⊆ X

X and X

⊆ X

X are then the

;

3

3 6

;

; 6

upward and downward closure operations. A set X is said to be a

for

cover

a set Y in

if Y

X

. A point x is called an

in

if

x

P .

atom

F

F

ff

;

f

g ?

THEOREM 1.6

⊆

W" R" P

n

Suppose

is a transitive re.ned

5generated

F

frame. for some

: Then

n 5 '

h

i

n

(i)

3

each cluster in

contains

points'

F

(ii)

d

d(

)

W

W

'

for every .nite

.

is a cover for

and contains at

F

7

5

d

d

most

distinct clusters. where

c

(d)

n

7

c

(1) ⊆ 3

" 3

1"

c

(m " 1) ⊆ c

(1)

3

4

n

n

n

n

,

c

"""

c

m

n

n

1.9"

"

1

9

n

[

6

(iii)

every point of .nite depth in

is an atom:

F

Proof

F

(i) follows from the differentiatedness of

and the obvious fact that

precisely the same formulas (in p

" . . . " p

) are true under

at #-equivalent

.

n

V

points in the same cluster.

The proof of (ii) proceeds by induction on d. Let x

W

. Since

is

.d

F

transitive and W

is finite (by the induction hypothesis). there exists a

,

d

?

non-empty upward closed in W

set X (i.e. X ⊆ X

W

) such that

.d

.d

x

X

. points in X see exactly the same points of depth

d and either

3 0

?

;

7

u" v

X

w

u

X w

v

(1)

?

)

?

1

?

3 0

2

or

u" v

X (u

v

uRv).

(3)

?

)

?

2

. -

Such a set X is called

4 it is

if (1) holds and

dfficyclic

nondegenerate

degenerate

otherwise. One can readily show that the same formulas are true at #-

equivalent points in X . Since

is refined. X is then a cluster of depth

F

d " 1. Thus. W

W

. The upper bound for the number of distinct

.d

d

5

".

clusters of depth d " 1 follows from the differentiatedness of

and the

F

ff

;

definition of d-cyclic sets.

To establish (iii). for every point x of depth d " 1 one can construct

by induction on d a formula (expressing the definition of the d-cyclic set

containing x) which is true in

under

only at x. For details consult

F

V

[Chagrov and Zakharyaschev 1998].

.

It is fairly easy now to construct the (generated) subframe

K.

?

(n) of the

.

F

universal frame of rank n for

consisting of finite depth points. Indeed.

K,

FK.

(n) is n-generated. refined and so has the form as described in Theo-

rem 1.6. On the other hand. it is universal and contains any n-generated

descriptive frame as a generated subframe. which means roughly that it con-

tains all possible points of finite depth that can exist in n-generated refined

frames.

5(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

,

p

.

F

,

(1)

P

S.

a

H

P

P

a

P

Q

c

P

:

Q

b

c

H

o

P

a

o

b

Q

P

Q

?

:

Φ

?

"

,

C

S

'

"

5

S

'

5

A

.

A

c

.

H

:

.

C

P

a

:

c

,

P

,

.

A

P

"

.

'

.

C

b

,

C

S

'

Q

a

P

,

5

S

Q

H

?

"

,

5

A

,

C

S

'

,

5

P

S

b

H

"

,

5

A

.

A

"

P

.

'

.

C

c

:

P

a

:

c

b

P

P

H

Q

P

Q

?

a

c

:

:

a

c

P

Q

P

Q

?

a

P

b

P

H

.

A

c

"

.

P

'

:

.

C

,

C

S

'

:

Q

,

5

a

S

P

c

Q

?

H

"

,

5

A

P

b

a

P

P

H

c

Q

P

?

Q

:

,

C

S

'

,

5

S

P

"

,

H

5

A

.

A

"

.

'

P

.

C

:

a

c

b

.

"

A

.

'

P

.

C

:

a

c

P

P

c

:

H

Q

?

P

Q

b

a

P

,

C

,

S

'

5

Q

?

S

a

"

,

Q

P

b

5

H

A

,

C

,

S

'

5

S

"

,

5

P

H

A

.

"

A

.

'

.

P

C

:

c

a

b

P

c

:

?

Q

Q

P

:

a

c

c

:

P

P

Q

?

Q

P

a

P

b

H

a

P

H

P

b

,

:

C

,

S

5

'

?

Q

"

S

,

c

5

a

Q

.

"

A

.

c

:

'

.

P

C

b

P

H

A

o

p
o

p
o

o

p
o

o

p
o

o

p
o

o

.

.

.

.

.

Φ

Φ

Φ

Φ

Φ

Φ

Figure 3.

More precisely. assuming that each point is assigned the set of variables

in # that are true at it. we begin constructing a frame

(n) by putting

GK.

n

n

,

at depth 1 in it 3

non-#-equivalent degenerate clusters and 3

1 non-

#-equivalent non-degenerate clusters with

3

non-#-equivalent points.

n

[

Suppose that

(n) is already constructed. Then for every antichain

of

K.

d

G

,

7

a

clusters in

(n) containing at least one cluster of depth d and different

K.

d

G

,

from a singleton with a non-degenerate cluster. we add to

(n) copies

K.

d

G

,

n

,

n

of all 3

" 3

1 clusters of depth 1 so that they would be inaccessible

from each other and could see only the clusters in

and their successors.

a

[

And for every singleton

⊆

C

with a non-degenerate cluster C . we add

a

d

f

g

to

(n) copies of those clusters of depth 1 which are not #-equivalent to

K.

G

,

any subset of C (otherwise the frame will not be refined) so that again they

would be mutually inaccessible and could see only C and its successors in

d

G

,

K.

(n).

Let

(n) ⊆

(n)"

(n)

be the resulting model (the relational

NK.

GK.

UK.

component of

(n) is completely determined by the construction and its

GK.

h

i

set of possible values is the collection of the truth-sets of formulas in

(n)

GK.

under

(n)). It is not hard to show that

(n) is atomic. Moreover. for

UK.

GK.

every point x in this frame one can construct a formula .(p

" . . . " p

) such

.

n

that x

⊆ . and. for any frame

.

⊆ . iff there is a generated subframe of

F

F

F

reducible to the subframe of

(n) generated by x. It follows in particular

GK.

'j

'j

that

(n) is refined. Thus. every

(n) is a generated subframe of

K.

GK.

G

,

d

FK.

FK.

(n). On the other hand. by Theorem 1.6.

(n) contains no clusters

of depth

d different from those in

(n) and so

(n) is isomorphic to

K.

K.

?

G

,

F

d

.

GK.

K,

(n). It worth noting also that. since

has the finite model property.

7

it is characterized by

(n). and so

(n) is isomorphic to the bidual of

K.

?

F

FK.

.

.

F

K.

?

(n).

The universal frame

(n) for an arbitrary consistent logic L in NExt

L

F

K,

is a generated subframe of

(n).

It can be constructed by removing

FK.

ADVANCED MODAL LOGIC

5)

from

(n) those points at which some formulas in L are refuted (under

FK.

VK.

F

F

(n)). For example.

S.

?

(n) is obtained by removing from

K.

?

(n)

.

.

all irreflexive points and their predecessors. In other words.

S.

?

(n) can

.

F

be constructed in the same way as

.

F

K.

?

(n) but using only non-degenerate

clusters.

(1) (the corresponding model. to be more exact) is shown in

S.

,

F

,

Fig. 3. where

denotes the cluster with two points at one of which p

is

.

true. To construct

(n) and

(n). we take only simple clusters and

Grz

GL

?

?

F

F

Φ

.

.

degenerate clusters. respectively.

In general. this method of constructing universal frames does not work

for logics with nontransitive frames. However. using the fact that

is

K

characterized by the class of finite intransitive irreflexive trees (see Section

12 of

). in the same manner as above one can construct

Basic Modal Logic

an intransitive irreflexive model characterizing

and such that

(n) is

K

FK

isomorphic to the bidual of the frame associated with this model.

Let us consider now the semantical meaning of splittings. In view of the

following observation we focus attention only on splittings by the logics of

finite rooted frames.

THEOREM 1.9

L

NExtL

L

If

splits

and

has the .nite model property

.

.

.

then

. for some .nite rooted frame

validating

:

L

⊆ Log

.

L

.

F

F

Proof

Since L

in the splitting pair (L

" L

) is a proper extension of L

.

,

.

,

.

there is a finite frame

such that

⊆ L

and

⊆ L

. It follows that

.

,

G

G

G

Log

L

. As we shall see later (Corollary 1.66). every extension of a

G

j

'j

.

ff

tabular logic is also tabular. So L

⊆ Log

for some finite

⊆ L

. And

.

.

F

F

since L

is

!prime.

must be rooted.

.

F

j

.

T

We say that a frame

NExtL

if Log

splits NExtL

. The logic L

splits

.

.

,

F

F

of the splitting pair (Log

" L

) is denoted by L

,

and called the

splitting

,

.

F

F

of NExtL

by

. This notation reflects the fact that L

is the smallest logic

.

,

F

in NExtL

which is not validated by

.

.

F

EXAMPLE 1.10 We show that

⊆

,

. Recall that

⊆

is

D

K

D

K

,

characterized by the class of serial frames (in which every point has a suc-

5

"

]

cessor). So if

⊆ L then L

Log

4 otherwise no frame for L has a dead

end. which means that

L and

L. The inconsistent logic

can

D

For

5 j

ff

5

,

be represented as

,

.

D

o

] ?

ff

To illustrate some applications of splittings we require a few definitions.

Given L

NExtL

. we say that the

for L above

axiomatization problem

.

L

is decidable if the set

. : L

. ⊆ L

is recursive. L is

strictly

.

.

?

Kripke complete

above L

if no other logic in NExtL

has exactly the same

.

.

f

"

g

Kripke frames as L. If all frames in a set

split NExtL

. we call the logic

.

L

,

:

the

of NExtL

and denote it by L

,

.

unionffisplitting

.

.

.

F

F

F

f

? F g

F

L

50

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

EXAMPLE 1.11

is not a splitting of NExt

. However. it is a union-

Grz

S,

o

"

splitting:

⊆

,

"

.

.

⊆

,

. A frame may split the

Grz

S,

S,

:

S,

lattice NExtL

,

but not NExtL

: e.g.

splits NExt

,

but does not

K

.

.

,

:

,

:

,

:

split NExt

.

K

F

o

5

.

.

.

.

.

.

o o

o o

o o

f

g

THEOREM 1.13

L

NExtL

L ⊆ (. . . (L

,

), . . .),

Suppose

and

n

. for

.

.

.

a sequence

of sets of .nite rooted frames:

.

" . . . "

n

F

F

n

?

F

F

(i)

If

⊆

is .nite and

is decidable then the axiomatization

L

i

5.

i

F

F

problem for

above

L

L

is decidable: More precisely.

S

.

. : L

. ⊆ L

⊆

.

L :

⊆ .

.

.

F

F

f

"

g

f

?

)

? F

'j

g

(ii)

L

L

L

.

If

is Kripke complete then

is strictly Kripke complete above

:

(iii)

L

NExtL

The immediate predecessors of

in

are precisely the logics

.

L

Log

. for

such that

is not a reduct of a generated subframe of

F

F

F

0

? F

another frame in

:

F

Proof

(i) is left to the reader as an easy exercise.

(ii) Let L

be a logic in NExtL

with the same Kripke frames as L. Then

.

.

obviously L

L. On the other hand. the frames in

do not validate L

.

.

ff

F

and so L

L

.

.

ff

(iii) If L

is an immediate predecessor of L in NExtL

then

⊆ L

. for

.

.

.

F

some

. Therefore. L

L

Log

L and so L

⊆ L

Log

. Suppose

.

.

F

F

F

j

now that

is not a reduct of a generated subframe of another frame in

F

? F

ff

0

—

0

and L

Log

L

L. Then L

Log

for some

. and hence

.

.

.

.

F

F

F

F

0

ff

—

ff

? F

.

F

F

F

.

.

⊆

. L

⊆ L

Log

.

0

As follows from Theorem 1.13 and Example 1.10.

has exactly two

For

immediate predecessors

⊆ Log

and

⊆ Log

(and each consis-

Verum

Triv

tent normal modal logic is contained in one of them). This result is known

5

o

as Makinson's [1981] Theorem. Moreover. the axiomatization problem for

For

is decidable. i.e. there is an algorithm which decides. given a formula

. whether

. is consistent. Likewise. since

⊆

is decidable.

K

D

K

,

there is an algorithm recognizing. given . whether

⊆

. We shall

D

K

"

"

]

see later in Section 5.5 that in fact not so many properties of logics are

"

decidable (e.g. the axiomatization problem for

is undecidable4

K

,

see Theorem 5.17) and that Theorem 1.13 (i) provides the main method for

" -

]

proving decidability results of this type.

To determine whether a finite rooted frame

⊆

W" R

splits NExtL

.

.

F

we need the formulas defined below:

h

i

 F ⊆

p

p

: x" y

W" xRy

x

y

,

f

.

?

g 6

p

x

p

: x" y

W"

xRy

y

,

f

. -

?

-

g 6

p

p

: x" y

W" x

⊆ y

"

x

y

f

. -

?

g

'
ADVANCED MODAL LOGIC

5?

1F ⊆

 F " 9F ⊆ 1F

p

: x

W

.

x

.

"

.

f

?

g

The meaning of 9F is explained by the following lemma. in which

.,

n

.

.

. ⊆

. : n 5 '

.

f

g

LEMMA 1.12

r

For any .nite

with root

. the set of formulas

p

r

9F

F

.,

.

is satis.able in a frame

i, there is a generated subframe

of

reducible

G

H

G

f

g 6

to

: Moreover. if

is cycle free ?i:e:. contains no path from a point to

F

F

itself " then

can be replaced by

'

n ⊆ d(

) " 1

:

F

Proof

G

(

) Suppose

p

9F is satisfied at a point u in

. It is not

r

.,

.

hard to check that the map f defined by f (v) ⊆ x iff v

⊆ p

is a reduction of

x

8

f

g 6

the subframe

of

generated by u to

. If

is cycle free and

p

9F

r

H

G

F

F

j

.,

.

is satisfied at u then d(

) ⊆ d(

). For otherwise an ascending chain of n " 1

H

F

f

g 6

points starts from u and so

must contain a cycle.

F

(

) Let f be a reduction of

to

. Define a valuation in

so that

H

F

G

⊆

.

v

⊆ p

iff v

f

(x). The reader can readily verify that under this

x

5

j

?

.,

.

valuation

p

9F is true at any point in f

(r).

r

5

.

.

f

g 6

LEMMA 1.15

L

NExt

For every logic

and every .nite rooted frame

.

K

F

F

.

⊆ L

n 5 '

9F

p

i,

L

:

,

r

n

?

j

)

. -

'?

Proof

The implication (

) follows from Lemma 1.12. Suppose now that

n

8

.,

.

.

,

r

r

9F

p

L. for every n 5 ' . Then the set

p

9F is L-

consistent and so it is satisfied in a frame

for L. By Lemma 1.12. a

G

. -

'?

f

g 6

generated subframe of

is reducible to

. and hence

⊆ L.

G

F

F

.

j

We are now in a position to characterize finite frames that split NExtL

.

and to axiomatize splittings.

THEOREM 1.17

r

L

NExt

Suppose

is a .nite frame with root

and

K

:

F

.

?

Then

splits

i, there is

such that. for every frame

NExtL

n 5 '

.

⊆ L

.

.

F

G

n

m

j

.

.

,

r

9F

p

,

r

9F

p

is satis.able in

only if

is satis.able in

for every

G

G

m " n

L

,

⊆ L

9F

: In this case

p

:

r

.

.

,

F

.

.

n

.

"

. -

Proof

G

(

) Suppose otherwise and consider a sequence

: n 5 '

of

n

frames for L

such that

9F

p

is satisfiable in

but

9F

p

is

.

,

r

n

r

,

.

.

G

8

n

f

m

g

not satisfied. for some m " n. By Lemma 1.15. the former condition implies

.

.

n.,

Log

Log

. while the latter means that

⊆ Log

. for every

n

n

G

F

F

G

n 5 ' . contrary to Log

being

!prime.

F

T

ff

'j

(

) We show that L

,

⊆ L

9F

p

. Suppose L

Log

.

F

F

.

.

T

,

r

n

.

⊆

"

. -

'ff

m

.

Then. by Lemma 1.15. there is m 5 ' such that

9F

p

L. It

,

r

follows that

9F

p

L and so L

9F

p

L.

,

r

.

,

r

.

.

.

n

n

. -

?

. -

?

"

. -

ff

5fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

For more general versions of this criterion consult [Kracht 1990] and

[Wolter 1992].

COROLLARY 1.16 (Rautenberg 1960)

L

NExt(

Suppose that

.

K

tra

n

)

.

for some

: Then every .nite rooted frame

for

splits

and

n 5 '

L

NExtL

.

.

F

?

"

L

,

⊆ L

9F

.

.

,

p

:

r

F

n

.

"

. -

In particular. every transitive finite rooted frame splits NExt

. This

K,

result may also be obtained using the fact that all finite subdirectly irre-

ducible algebras split the lattice of subvarieties of a variety with equationally

definable principal congruences (see [Blok and Pigozzi 1963]). However. not

every frame splits NExt

.

K

THEOREM 1.18 (Blok 1986)

NExt

A .nite rooted frame

splits

i, it is

F

K

cycle free: In this case

,

⊆

9F

p

n ⊆ d(

)

. where

:

,

r

K

K

F

F

n

.

"

. -

Proof

K

That frames with cycles do not split NExt

follows from the fact

that

is characterized by cycle free finite rooted frames. And the converse

K

is an immediate consequence of Lemma 1.12 and Theorem 1.17.

.

An element x

⊆ 0 of a complete lattice

is called an

in

if the zero

atom

L

L

element 0 in

is the immediate predecessor of x. i.e. there is no y such that

L

0 5 y 5 x. Splittings turn out to be closely related to the existence of atoms

in finitely generated free algebras4 see [Blok 1986]. [Bellissima 1965. 1991]

and [Wolter 1998c]. We demonstrate the use of splittings by the following

THEOREM 1.16 (Blok 1960a)

NExt

The lattice

has no atoms:

K

Proof

K

If a logic L is an atom in NExt

. it is

!prime. It follows that

L cosplits NExt

and the logic L

⊆ Log

in the splitting pair (L

" L)

.

.

K

F

L

has no proper predecessor that splits NExt

. Add a new irreflexive root

K

to

. By Theorem 1.18. the resulting frame

splits NExt

. and clearly

F

G

K

Log

Log

. which is a contradiction.

G

F

.

—

A logic is linked with its semantics via completeness theorems. The most

general completeness theorem states that every consistent normal modal

logic is characterized by the class of (descriptive) frames validating it. Or.

if we want to characterize the consequence relations

and

. we can use

L

.

L

"

"

the following

THEOREM 1.19 (i)

L

NExt

Φ

.

For

K

.

i, for any model

based on

L

M

a frame for

and any point

in

.

implies

L

x

x

⊆ Φ

x

⊆ .

:

M

?

"

(ii)

L

NExt

Φ

.

For

K

.

i, for any model

based on a frame for

M

j

j

?

"

.

L

L

.

⊆ Φ

implies

⊆ .

:

M

M

j

j

'
ADVANCED MODAL LOGIC

5'

However. usually more specific completeness results are required. What

is the "geometry" of frames for a given logic? Are Kripke or even finite

frames enough to characterize it? Questions of this sort will be addressed

in the next several sections.

.,: Persistence

The structure of Kripke frames for many standard modal logics can be

described by rather simple conditions on the accessibility relation which

are expressed in the first order language with equality and a binary (ac-

cessibility) predicate R. (This observation was actually the starting point

of investigations in

studying the relation between

Correspondence Theory

modal and first (or higher) order languages4 see Chapter 5 of this volume.)

Moreover. in many cases it turns out that the universal frame

(') for such

L

F

a logic L also satisfies the corresponding first order condition 8. Since 8 says

nothing about sets of possible values in P

('). it follows immediately that

L

the canonical (Kripke) frame

(') also satisfies 8 and so characterizes

L

.

F

L. Thus we obtain a completeness theorem of the form:

.

L iff

⊆ . for every Kripke frame

satisfying 8.

F

F

?

j

This method of establishing Kripke completeness. known as the

method

of canonical models

. is based essentially upon two facts: first. that L is

characterized by its universal frame

(') and second. that L is "persistent"

L

F

under the transition from

(') to its underlying Kripke frame. Of course.

L

F

instead of

(') we can take any other class of frames

with respect to

L

F

which L is complete and try to show that L is

!

in the sense

persistent

C

that. for every

⊆

W" R" P

in

. if

⊆ L then

⊆

W" R

validates L

F

F

C

.

F

as well.

h

i

C

j

h

i

PROPOSITION 1.30

If a logic is both

9complete and

9persistent. then it

is complete with respect to the class

.

:

F

F

of Kripke frames:

C

C

f

? C g

It follows in particular that L is Kripke complete whenever it is

!.

or

!. or

!persistent. Since every descriptive frame for L is a generated

DF

R

D

subframe of a suitable universal frame for L. L is

!persistent iff it is

persistent with respect to the class of its universal frames. It is an open

D

problem. however. whether

. i.e.

(')!persistence. implies

!

canonicity

L

F

persistence. Here are two simple examples.

D

THEOREM 1.31 (van Benthem 1962)

A logic is persistent with respect to

the class of al l general frames i, it is axiomatizable by a set of variable free

formulas:

ff[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

It is easily checked that a Kripke frame validates

iff no point in it

n

Alt

has more than n distinct successors (see [Segerberg 1981]).

THEOREM 1.33 (Bellissima 1966)

L

NExt

Every

is

9persistent.

Alt

n

for any

n 5 '

:

?

DF

Proof

The proof is based on the fact that. for any differentiated frame

F

⊆

W" R" P

. any finite X

W . and any y

X . there is Y

P such

h

i

ff

?

?

that X

Y ⊆

y

. It follows that at most n distinct points are accessible

from every point in a differentiated frame for L4 in particular.

is

!

n

Alt

0

f

g

persistent. Suppose now that a formula .

L is refuted at a point x under a

DF

valuation

in

.

a differentiated frame for L. Let X be the set of points

V

F

F

.

?

accessible from x in

md(.) steps.

Since X is finite. there is a valuation

8

U

F

U

V

in

such that

(p)

X ⊆

(p). for every variable p. Consequently. . is

7

false in

at x under

. which is a contradiction.

F

U

.

0

The proof of Fine's [1985c] Theorem that all logics of finite width. i.e.

logics in NExt

. for n 5 ' . are Kripke complete (a sketch can be

n

KfiBW

found in Section 16 of

) may also be regarded as a proof

Basic Modal Logic

of persistence. Recall that a point x in a transitive frame

⊆

W" R" P

F

is called

(relative to R) if there is X

P such that x

X

nonffieliminable

h

i

but no proper successor of x is in X (in other words. x is

in

maximal

?

?

X )4 in this case we write x

max

X . Denote by W

the set of all non-

R

r

eliminable points in

and put

⊆

W

" R

" P

. where R

⊆ R

W

.

r

r

r

r

r

r

F

F

.

?

P

⊆

X

W

: X

P

. (Fine called the frame

r

r

F

r

reduced

.)

h

i

f

0

?

g

THEOREM 1.32 (Fine 1967)

⊆

W" R" P

Let

be a transitive descriptive

F

frame and

: Then

there exists a point

x

X

P

(i)

y

max

X

x

and

R

h

i

(ii)

r

is a re.ned frame whose dual

is isomorphic to

:

F

F

F

r

?

?

?

0

3

"

"

Proof

(i) Suppose otherwise. i.e. there is no maximal point in X

x

.

Let Y be a maximal chain of points in X

x

(that it exists follows from

0

3

Zorn's Lemma) and

⊆

Z

P :

y

Y y

Y

Z

. Clearly.

is

0

3

non-empty and has the finite intersection property (because X

x

has no

X

f

?

1

?

3 0

ff

g

X

maximal point). By compactness. we then have a point z in

which. by

0

3

tightness. is maximal in Y . contrary to X

x

having no maximal point.

X

0

3

T

(ii) is a consequence of (i).

.

It follows that to establish the Kripke completeness of a logic L

NExt

K,

it is enough to show that it is persistent with respect to the class

?

⊆

:

a finitely generated descriptive frame

.

r

F

F

RE

f

g

That is what Fine [1985c] actually did for logics of finite width.

5

Here

]

7- the modal degree of

- is the length of the longest chain of nested modal

md

.

.

operators in

8

.

ADVANCED MODAL LOGIC

ff5

THEOREM 1.35 (Fine 1985c)

Al l logics of .nite width are

9persistent

and so Kripke complete:

RE

Let us return. however. to the method of canonical models. Having tried

it for a number of standard systems. Lemmon and Scott [1988] found a

rather general sufficient condition for its applicability and put forward a

conjecture concerning a further extension (which was proved by Goldblatt

[1986b]). This direction of completeness (and correspondence) theory culmi-

nated in the theorem of Sahlqvist [1987] who proved an optimal (in a sense)

generalization of the condition of [Lemmon and Scott 1988]. To formulate it

we require the following definition. Say that a formula is

(

)

positive

negative

if it is constructed from variables (negated variables) and the constants

.

]

using

.

.

and

.

,

.

:

.

,

THEOREM 1.37 (Sahlqvist 1987)

Suppose

is a formula which is equiva5

.

lent in

to a formula of the form

. where

.

is positive

(:

?)

k

0

?

K

k

.

and

is constructed from variables and their negations.

and

with the

:

.

9

help of

.

.

and

in such a way that no

1s subformula of the form

:

.

,

:

]

:

:

:

or

. containing an occurrence of a variable without

. is in the

.

,

.

.

,

,

,

-

scope of some

: Then one can efiectively construct a .rst order formula

.

8(x)

R

in

and

having

as its only free variable and such that. for every

⊆

x

descriptive or Kripke frame

and every point

in

.

a

F

F

F

F

(

" a)

⊆ .

⊆ 8(x)[a].

i,

j

j

?Here

means that

is true at

in

under any valuation:"

(

" a)

⊆ .

.

a

F

F

j

Proof

We present a sketch of the proof found by Sambin and Vaccaro

[1969]. Given a formula .(p

" . . . " p

). a frame

⊆

W" R" P

and sets

.

n

F

X

" . . . " X

P . denote by .(X

" . . . " X

) the set of points in

at which .

.

.

n

n

h

i

F

is true under the valuation

defined by

(p

) ⊆ X

. i.e. .(X

" . . . " X

) ⊆

i

i

n

.

V

V

?

V

(.). Using this notation. we can say that

F

(

" x)

⊆ .(p

" . . . " p

) iff

X

" . . . " X

P x

.(X

" . . . " X

).

.

.

.

n

n

n

j

)

?

?

EXAMPLE 1.36 Let us consider the formula

p

p and try to extract

.

a first order equivalent for it in the class of tight frames directly from the

.

equivalence above and the condition of tightness. For every tight frame

F

⊆

W" R" P

we have:

h

i

F

.

.

(

" x)

⊆

p

p iff

X

P x

(

X

X )

j

.

)

?

?

.

iff

X

P (x

X

x

X )

.

)

?

?

.

?

iff

X

P (x

X

x

X ).

)

?

3 ff

.

?

ffff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

To eliminate the variable X ranging over P . we can use two simple obser-

vations. The first one is purely set-theoretic:

X

P (Y

X

x

X ) iff x

X

P : Y

X

.

(2)

)

?

ff

.

?

?

f

?

ff

g

,

And the second one is just a reformulation of the characteristic property of

tight frames:

With the help of (2) and (5) we can continue the chain of equivalences above

X

P : x

X

⊆ x

.

(5)

f

?

3 ff

g

3

,

with two more lines:

F

.

(

" x)

⊆

p

p iff . . .

j

.

iff x

X

P : x

X

?

f

?

3 ff

g

iff x

x

.

T

?

3

Thus.

⊆

p

p iff

x x

x

iff

x xRx.

F

.

j

.

)

?

3

)

The proof of Sahlqvist's Theorem is a (by no means trivial) generalization

of this argument. Define by induction x

⊆

x

. x

⊆ (x

)

. and notice

.

".

n

n

that in (5) we can replace x

by any term of the form x

. . .

x

.

.

k

3

f

g

3

3

3

n

.

n

k

thus obtaining the equality

3

3

6

6

3

X

P : x

. . .

x

X

⊆ x

. . .

x

(7)

.

.

k

k

n

.

n

k

n

.

n

k

f

?

3

6

6

3

ff

g

3

6

6

3

,

which holds for every tight frame

⊆

W" R" P

. all x

" . . . " x

W and all

.

k

F

n

" . . . " n

0.

.

k

9

n

.

n

k

h

i

?

A frame-theoretic term x

. . .

x

with (not necessarily distinct)

.

k

world variables x

" . . . " x

will be called an R-

. It is not hard to see

term

.

k

3

6

6

3

that for any R-term T . the relation x

T on

⊆

W" R" P

is first order

F

expressible in R and ⊆. Consequently. we obtain

?

h

i

LEMMA 1.38

.(p

" . . . " p

)

T

" . . . " T

Suppose

is a modal formula and

are

.

n

.

n

R

x

.(T

" . . . " T

)

5terms: Then the relation

is expressible by a .rst order

.

n

formula ?in

and

" having

as its only free variable:

R

⊆

x

?

Syntactically. R-terms with a single world variable correspond to modal

formulas of the form

p

. . .

p

with not necessarily distinct

.

k

m

m

.

k

.

.

propositional variables p

" . . . " p

. Such formulas are called

.

strongly positive

.

k

.

.

By induction on the construction of . one can prove the following

LEMMA 1.36

.(p

" . . . " p

)

Suppose

is a strongly positive formula contain5

.

n

ing al l the variables

and

is a frame: Then one

p

" . . . " p

⊆

W" R" P

.

n

F

can efiectively construct

5terms

?of one variable

" such that

R

T

" . . . " T

x

.

n

h

i

for any

and any

x

W

X

" . . . " X

P

.

.

n

?

?

x

.(X

" . . . " X

)

T

X

. . .

T

X

.

i,

.

.

.

n

n

n

?

ff

.

.

ff

ADVANCED MODAL LOGIC

ff—

Now. trying to extend the method of Example 1.36 to a wider class of

formulas. we see that it still works if we replace the antecedent

p in

p

p

.

.

with an arbitrary strongly positive formula : . As to generalizations of the

.

consequent. let us take first an arbitrary formula ? instead of p and see

what properties it should satisfy to be handled by our method.

Thus. for a modal formula (:

?)(p

" . . . " p

) with strongly positive :

.

n

and a tight frame

⊆

W" R" P

. we have:

F

.

h

i

F

(

" x)

⊆ :

? iff

X

" . . . " X

P (x

:(X

" . . . " X

)

.

.

n

n

j

.

)

?

?

.

x

?(X

" . . . " X

))

.

n

?

iff

X

" . . . " X

P (T

X

. . .

T

X

.

.

.

n

n

n

)

?

ff

.

.

ff

.

x

?(X

" . . . " X

))

.

n

?

iff

X

" . . . " X

P (T

X

. . .

T

X

.

.

.

.

.

.

n

n

n

)

?

ff

.

.

ff

.

5

5

5

X

P (T

X

x

?(X

" . . . " X

))).

n

n

n

n

.

)

?

ff

.

?

(2) does not help us here. but we can readily generalize it to

X

P (Y

X

x

?(. . . " X" . . .)) iff

)

?

ff

.

?

x

?(. . . " X" . . .) : Y

X

P

.

(6)

?

f

ff

?

g

,

So

F

(

" x)

⊆ :

? iff

X

" . . . " X

P (T

X

. . .

T

X

.

.

.

.

.

.

n

n

n

j

.

)

?

ff

.

.

ff

.

5

5

5

x

?(X

" . . . " X

) : T

X

P

).

.

n

n

n

?

f

ff

?

g

,

But now (5) and (7) are useless. In fact. what we need is the equality

?(. . . " X" . . .) : T

X

P

⊆

f

ff

?

g

,

?(. . . "

X

P : T

X

" . . .)

(8)

f

?

ff

g

,

which. with the help of (7). would give us

?(. . . " X" . . .) : T

X

P

⊆ ?(. . . " T " . . .).

(6)

f

ff

?

g

,

Of course. (8) is too good to hold for an arbitrary ?. but suppose for a

moment that our ? satisfies it. Then we can eliminate step by step all the

variables X

" . . . " X

like this:

.

n

F

(

" x)

⊆ :

? iff

X

" . . . " X

P (T

X

. . .

T

X

.

.

.

.

.

.

n

n

n

j

.

)

?

ff

.

.

ff

.

5

5

5

x

?(X

" . . . " X

" T

))

.

.

n

n

?

5

iff . . . (by the same argument)

iff x

?(T

" . . . " T

).

.

n

?

ff(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

And the last relation can be effectively rewritten in the form of a first order

formula 8(x) in R and ⊆ having x as its only free variable. So. finally we

shall have

⊆ :

? iff

x 8(x).

F

j

.

)

Now. to satisfy (8). ? should have the property that all its operators

distribute over intersections. Clearly.

and

are not suitable for this goal.

But all the other operators turn out to be good enough at least in descriptive

.

-

and Kripke frames. So we can take as ? any positive modal formula. The

main property of a positive formula .(. . . " p" . . .) is its

in every

monotonicity

variable p which means that. for all sets X . Y of worlds in a frame. X

Y

ff

implies .(. . . " X" . . .)

.(. . . " Y " . . .).

ff

To prove that all positive formulas satisfy (8) in Kripke frames and de-

scriptive frames. recall that

distributes over arbitrary intersections in

.

any frame. As to

. we have the following lemma in which a family

of

,

non-empty subsets of some space W is called

if for all

downward directed

X

X" Y

there is Z

such that Z

X

Y .

? X

? X

ff

0

LEMMA 1.39 (Esakia 1985)

⊆

W" R" P

Suppose

is a descriptive frame:

F

Then for every downward directed family

P

.

h

i

X ff

,

,

X ⊆

X.

X

X

,

,

:X

:X

Using Esakia's Lemma. by induction on the construction of . one can

prove

LEMMA 1.20

⊆

W" R" P

Suppose that

is a Kripke or descriptive frame

F

and

is a positive formula: Then for every

and al l

.(p" . . . " q " . . . " r)

Y

W

h

i

U" . . . " V

P

.

ff

?

,

.(U" . . . " X" . . . " V ) : Y

X

P

⊆

f

ff

?

g

.(U" . . . "

X

P : Y

X

" . . . " V ).

(9)

f

?

ff

g

,

It follows from this lemma and considerations above that Sahlqvist's The-

orem holds for formulas . ⊆ :

? with strongly positive : and positive

?. The remaining part of the proof is purely syntactic manipulations with

.

modal and first order formulas.

Notice that using the monotonicity of positive formulas. equivalence (6)

can be generalized to the following one:

for every

⊆

W" R" P

. every

F

positive ?

(. . . " p" . . .) and every x

W .

i

i

?

h

i

X

P (Y

X

x

?

(. . . " X" . . .)) iff

i

i

)

?

ff

.

?

i

n

"

,

x

i

?

(. . . " X" . . .) : Y

X

P

.

(10)

i

?

f

ff

?

g

i

n

"

,

,

ADVANCED MODAL LOGIC

ff)

Say that a modal formula : is

if it can be constructed from negative

untied

formulas and strongly positive ones using only

and

. If 0 (p

" . . . " p

) is

.

n

,

negative then

0 (p

" . . . " p

) is clearly equivalent in

to a positive formula4

.

n

.

K

we denote it by 0

(

p

" . . . "

p

).

.

.

n

-

-

-

LEMMA 1.21

:(p

" . . . " p

)

⊆

W" R" P

Let

be an untied formula and

a

.

n

F

h

i

frame: Then for every

and al l

x

W

X

" . . . " X

n

P

.

.

?

?

x

:(X

" . . . " X

)

i,

y

" . . . " y

(ff

T

X

z

0

(X

" . . . " X

))

.

.

.

n

l

i

i

j

j

n

?

1

.

ff

.

?

i

n

j

m

.

.

,

,

where the formula in the rightffihand side. efiectively constructed from

. has

:

only one free individual variable

.

is a conjunction of formulas of the form

x

ff

uRv

T

R

0

(p

" . . . " p

)

.

are suitable

5terms and

are negative formulas:

i

j

n

.

We are ready now to prove Sahlqvist's Theorem. To construct a first order

equivalent for

(:

?) supplied by the formulation of our theorem. we

k

.

observe first that one can equivalently reduce : to a disjunction :

. . .

:

.

m

.

of untied formulas. and hence

(:

?) is equivalent in

to the formula

K

k

.

,

,

k

k

.

.

.

(:

?)

. . .

(:

?). So all we need is to find a first order

.

m

equivalent for an arbitrary formula

(:

?) with untied : and positive ?.

.

.

.

.

k

.

Let p

" . . . p

be all the variables in : and ? and

⊆

W" R" P

a descriptive

.

n

.

F

or Kripke frame. Then. for any x

W . we have:

h

i

?

F

.

.

(

" x)

⊆

(:

?) iff

X

" . . . " X

P x

(:

?)(X

" . . . " X

)

.

.

n

n

k

k

j

.

)

?

?

.

k

(by Lemma 1.21) iff

X

" . . . " X

P

y (xR

y

(

y

" . . . " y

(ff

.

.

n

l

)

?

)

.

1

.

T

X

z

0

(X

" . . . " X

))

i

i

j

j

n

.

ff

.

?

.

i

n

j

m

.

.

,

,

y

?(X

" . . . " X

)))

.

n

?

iff

X

" . . . " X

P

y " y

" . . . " y

(ff.

T

X

n

l

i

i

.

.

)

?

)

.

ff

.

i

n

.

,

z

0

(X

" . . . " X

)

y

?(X

" . . . " X

))

j

j

n

n

.

.

?

.

?

j

m

.

,

k

where ff

⊆ xR

y

ff. Let -

(p

" . . . " p

) ⊆ 0

(

p

" . . . "

p

). We continue

.

j

n

.

.

j

.

n

this chain of equivalences as follows:

.

-

-

iff

y " y

" . . . " y

l

(ff

.

X

" . . . " X

P (

T

X

n

i

i

.

.

)

. )

?

ff

.

i

n

.

,

z

-

(X

" . . . " X

)))

j

j

n

.

j

m

"

".

,

?

ff0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

(where -

(p

" . . . " p

) ⊆ ?(p

" . . . " p

) and z

⊆ y)

m

n

n

m

".

.

.

".

iff

y " y

" . . . " y

(ff

z

-

(T

" . . . " T

))"

.

.

.

l

j

j

n

)

.

?

j

m

"

".

,

as follows from (10). Lemma 1.20 and equality (7).

It remains to use

Lemma 1.38.

.

The formulas . defined in the formulation of Theorem 1.37 are called

Sahlqvist formulas

. It follows from this theorem that if L is a

!persistent

logic and Φ a set of Sahlqvist formulas then L

Φ is also

!persistent.

D

Moreover. L

Φ is

(in the sense that the class of Kripke frames

elementary

"

D

for it coincides with the class of all models for some set of first order formulas

"

in R and ⊆) whenever L is so.

Other proofs of Sahlqvist's Theorem were found by Kracht [1992] and

Joonsson [1995] (the latter is based upon the algebraic technique developed in

[Joonsson and Tarski 1971]). Venema [1991] extended Sahlqvist's Theorem to

logics with non-standard inference rules. like Gabbay's [1961a] irreflexivity

rule.

In [Chagrov and Zakharyaschev 1997b] it is shown that there is a

continuum of Sahlqvist logics above

and that not all of them have the

S,

finite model property (above

such a logic was constructed by Hughes

T

and Cresswell [1965]). As we shall see later in this chapter. there are even

undecidable finitely axiomatizable Sahlqvist logics in NExt

. It would be

K

of interest to find out whether such logics exist above

or

.

K,

S,

Kracht [1992] described syntactically the set of first order equivalents of

Sahlqvist formulas. To formulate his criterion we require the fragment

of

first order logic defined inductively as follows. Formulas of the form xR

y

S

m

are in

for all variables x" y and every m 5 ' 4 besides. if 8" 8

are in

then

.

S

S

the formulas

m

m

x

y

8"

x

y

8" 8

8. " and 8

8.

)

?

3

1

?

3

.

,

are also in

. For simplicity we assume that all occurrences of quantifiers

in a formula bind pairwise distinct variables. Call a variable y in a formula

S

8

if either all occurences of y are free in 8 or 8

inherently universal

? S

m

contains a subformula

y

x

8

which is not in the scope of

.

.

)

?

3

1

THEOREM 1.23 (Kracht 1992)

8(x)

R

For every .rst order formula

?in

and

" of one free variable

. the fol lowing conditions are equivalent"

⊆

x

(i) 8(x)

is classical ly equivalent to a formula

8

(x)

.

such that any sub5

formula of the form

of

contains at least one inherently universal

yR

z

8

(x)

.

m

? S

variable'

(ii) 8(x)

corresponds to a Sahlqvist formula in the sense of Theorem 8:0ff:

ADVANCED MODAL LOGIC

ff?

Condition (i) is satisfied. for example. by the formula

which corresponds to

p

p. On the other hand.

,.

.,

u

x

v

x

z

u

vRz

)

?

3 )

?

3 1

?

3

.

8(x) ⊆

y

x

z

y

zR

y

.

1

?

3 )

?

3

does not satisfy (i). In fact. even relative to

the condition expressed by

S,

8(x) does not correspond to any Sahlqvist formula. Notice. however. that

S,

.,

,.

p

p is a

-persistent logic whose frames are precisely the

"

.

D

transitive and reflexive frames validating

x8(x).

)

We conclude this section by mentioning two more important results con-

necting persistence and elementarity (the idea of the proof was discussed in

Section 33 of

.)

Basic Modal Logic

THEOREM 1.22 (i) (Fine 1987b. van Benthem 1960)

L

If a logic

is char5

acterized by a .rst order de.nable class of Kripke frames then

is

9

L

persistent:

D

(ii) (Fine 1987b)

L

If

is

5persistent then the class of Kripke frames for

L

is .rst order de.nable:

R

It is an open problem whether every

!persistent logic is determined by

a first order definable class of Kripke frames4 for more information about

D

this and related problems consult [Goldblatt 1997].

.," The degree of Kripke incompleteness

All known logics in NExt

of "natural origin" are complete with respect

K

to Kripke semantics. On the other hand. there are many examples of "ar-

tificial" logics that cannot be characterized by any class of Kripke frames

(see Sections 19. 30 of

Basic Modal Logic

or the examples below). To un-

derstand the phenomenon of Kripke incompleteness Fine [1985b] proposed

to investigate how many logics may share the same Kripke frames with a

given logic L. The number of them is called the

degree of Kripke incom5

pleteness

of L. Of course. this number depends on the lattice of logics under

consideration. The degree of Kripke incompleteness of logics in NExt

was

K

comprehensively studied by Blok [1986]. In this section we present the main

results of that paper following [Chagrov and Zakharyaschev 1998].

By Theorem 1.13. all Kripke complete union-splittings of NExt

have

K

degree of incompleteness 1. And it turns out that no other union-splitting

exists.

THEOREM 1.25 (Blok 1986)

NExt

Every unionffisplitting of

has the .nite

K

model property:

fffl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

nontransitive

.

.

.

.

k

.

k

k

k

k

x

x

x

5

x

x

x

x

x

x

x

x

x

x

.

.

,

n

.

.

.

,

.

,

.

n

n

.

.

.

. .

.

o

o

6 6 6

o

o

5

5

6 6 6

5

5

5

6 6 6

5

6 6 6

5

5

6 6 6

5

"

"

(a)

(b)

Figure 2.

Proof

Let

be a class of finite rooted cycle free frames. We prove that

L ⊆

,

has the finite model property using a variant of filtration. which

K

F

is applied to an n-generated refined frame

⊆

W" R" P

for L refuting a

F

F

formula .(p

" . . . " p

) under a valuation

.

.

n

V

h

i

Since

is differentiated. for every m

1 there are only finitely many

F

points x in

such that x

⊆

4 we shall call them

points of

5

F

.

.

m

m

9

.

type

m. Given

.

. the set of all subformulas in . we put

Sub

Sub

j

: . -

:

m

⊆ m if m is the minimal number such that a point in

is of type

m

0

F

ff

whenever x

⊆   and the formulas in

.

  are false at x (under

)4 if

Sub

7

V

no such m exists. we put m

⊆ 0. Let

0

j

[

k ⊆ max

m

:

.

" Φ ⊆

(.

).

Sub

Sub

0

k

.

f

ff

g

.

:

Now we divide

into two parts: W

consisting of points of type

k and

.

F

W

⊆ W

W

. For x" y

W . put x

y if either x" y

W

and x ⊆ y

,

.

.

7

or x" y

W

and exactly the same formulas in Φ are true at x and y . Let

[

?

2

?

,

?

N

G

U

⊆

"

be the smallest filtration (see Section 13 of

)

Basic Modal Logic

h

i

of

⊆

"

through Φ with respect to

. Since W

is finite.

is also

.

M

F

V

G

finite and. by the Filtration Theorem. (

" x)

⊆ : iff (

" [x])

⊆ : . for every

M

N

h

i

2

:

Φ. So it remains to show that

⊆ L. Notice that [x] in

is of type

G

G

j

j

?

j

m

k iff x has type m in

. Moreover. there is no [x] of type l " k . For

F

7

k

.

otherwise x

⊆

and m

⊆ 0 for   ⊆

:

. : x

⊆ :

. which

Sub

0

means that arbitrary long chains (of not necessarily distinct points) start

'j

:

f

?

j

g

from [x]. contrary to [x] being of type l. Thus

consists of two parts:

G

points of type

k . which form the generated subframe

W

" R

W

of

.

.

.

.

F

and points involved in cycles. Since

⊆ L and frames in

are cycle free.

F

7

h

i

it follows from Lemma 1.12 and Theorem 1.18 that

⊆ L.

G

.

j

F

j

THEOREM 1.27 (Blok 1986)

L

If a logic

is inconsistent or a unionffisplitting

of

. then

is strictly Kripke complete: Otherwise

has degree of

NExt

L

L

K

Kripke incompleteness

in

3

NExt

"

K

:

.

Proof

For

That

is strictly complete follows from Example 1.10 and The-

orem 1.13. Suppose now that a consistent L is not a union-splitting and L

.

ADVANCED MODAL LOGIC

ff'

is the greatest union-splitting contained in L. Since L

has the finite model

.

property. there is a finite rooted frame

⊆

W" R

for L

refuting some

F

h

i

.

F

.

L and such that every proper generated subframe of

validates L.

?

F

Clearly.

is not cycle free. Let x

Rx

R . . . Rx

Rx

be the shortest cycle

.

,

.

n

in

and k ⊆ md(.) " 1. We construct a new frame

by extending the

.

F

F

cycle x

" . . . " x

" x

as is shown in Fig. 2 ((a) for n ⊆ 1 and (b) for n " 1).

.

.

n

More precisely. we add to

copies x

" . . . " x

of x

for each i

1" . . . " n

.

i

i

i

F

.

k

organize them into the nontransitive cycle shown in Fig. 2 and draw an

? f

g

j

arrow from x

to y

W

x

" . . . " x

iff x

Ry . Denote the resulting frame

i

.

n

i

by

⊆

W

" R

and let x

⊆ x

. By the construction.

is a reduct of

.

.

.

.

.

.

n

F

F

F

?

[ f

g

k

Therefore. for every models

⊆

"

and

⊆

"

such that

.

.

.

M

F

V

M

F

V

h

i

h

i

h

i

V

V

V

. (p) ⊆

(p)

x

: x

(p)" j 5 k

i

i

j

6 f

?

g

and for every x

W . :

. we have (

" x)

⊆ : iff (

" x)

⊆ : . So we

.

Sub

M

M

can hook some other model on x

. and points in W will not feel its presence

.

?

?

j

j

by means of .'s subformulas. The frame to be hooked on x

depends on

.

whether

⊆ L or

⊆ L. We consider only the former alternative.

5 j

o j

Fix some m "

W

. For each I

'

0

. let

⊆

W

" R

" P

be the

.

I

I

I

I

F

frame whose diagram is shown in Fig. 5 (d

sees the root of

. all points

.

.

F

j

j

ff

[ f

g

h

i

e

and e

and is seen from x

4 the subframes in dashed boxes are transitive.

i

.

j

.

e

W

iff i

I . and P

consists of sets of the form X

Y such that X

.

i

I

I

?

?

6

is a finite or cofinite subset of W

b" a

: i 5 '

and Y is either a finite

I

i

subset of

a

: i 5 '

or is of the form

b

Y

. where Y

is a cofinite subset

i

.

.

[ f

g

of

a

: i 5 '

. It is not hard to see that the points a

. c. e

and e

are

i

i

i

.

i

f

g

f

g 6

f

g

characterized by the variable free formulas

—

⊆

(9

(9

. . .

9

) . . .)

(9

(9

. . .

9

) . . .)"

.

.

.

.

.

m

m

m

m

,

,

,

,

,

,

,

.

.

.

. -

.

.

.

5

5

—

⊆

—

—

" ( ⊆

—

—

"

i

i

i

".

.

.

,

,

,

,

,

,

. -

. -

)

⊆

( " )

⊆

)

)

" ).

⊆

)

)

"

.

".

".

i

i

i

i

i

i

".

,

,

,

,

,

,

"

. -

. -

(in the sense that x

⊆ —

iff x ⊆ a

. etc.). where

i

i

j

9

⊆

" 9

⊆

9

9

" 9

⊆

9

9

9

"

.

.

.

.

,

.

.

.

,.

,

,

,

"

:

. -

. -

. -

9

⊆

9

9

k

k

k

9

k

. . .

9

.

".

.

.

,

,

,

"

"

. -

. -

.

. -

5

Define L

to be the logic determined by the class of frames for L and

.

I

I

F

i.e. L

⊆ L

Log

. Since

()

.)

L

L

for i

I

J (. is

I

I

.

i

J

I

F

m

"8

,

refuted at the root of

).

L

: I

'

0

⊆ 3

.

.

I

"

F

0

-

.

-

?

[

?

[

.

Let us show now that L

has the same Kripke frames as L. Since L

L.

I

I

jf

ff

[ f

ggj

we must prove that every Kripke frame for L

validates L. Suppose there

I

ff

is a rooted Kripke frame

such that

⊆ L

but

⊆ : . for some :

L.

I

G

G

G

j

'j

?

—[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

nontransitive

transitive

1

F

1

.

1

H

x

.

"

H

.

H

c

b

a

i

a

a

d

d

d

.

d

m

.

.

.

.

.

.9

.

. .

. .

. .

5

5

o 6 6 6 5

5

5

6 6 6

5

5

5

6 6 6

5

5

5

"

0

0 0 0

ff

ff

ff

ff

ff-

ff

ff

ff

e

e

.

.

e

j

5

5

6 6 6

5

5

5

5

6 6 6

'I

'

"

transitive

'

"8

"

e

.

j

o

Figure 5.

Since : is in L. it is valid in all frames for L. in particular.

⊆ : . And

since :

L

. : is refuted in

. Moreover. by the construction of

. it

I

I

I

F

F

5 j

is refuted at a point from which the root of

can be reached by a finite

.

F

'?

number of steps. Therefore. the following formulas are valid in

and so

I

F

belong to L

and are valid in

:

I

G

l

i

,

:

( "

(11)

-

.

i

5.

"

l

i

:

((

(

(

p

p)

p))"

(13)

.

.

.

.

.

.

-

.

.

.

.

i

5.

.

where p does not occur in : and l is a sufficiently big number so that

any point in

is accessible by

l steps from every point in the selected

I

F

cycle and every point at which : may be false. and

? ⊆

(

—

?).

.

.

7

.

.

,

According to (11).

contains a point at which ( is true. By the construction

G

.

of ( . this point has a successor y at which. by (13).

(

p

p)

p is

.

.

.

.

true

in

and y

⊆

—

. Define a valuation

in

under any valuation

.

G

U

G

,

.

.

by taking

(p) ⊆ y

. Then y

⊆

(

p

p). from which y

⊆ p and so

.

.

U

.

.

j

y

y

. Now define another valuation

so that

(p) ⊆ y

y

. Since

.

.

U

U

3

j

.

j

?

3

3 [f

g

y is reflexive. we again have y

⊆

(

p

p). whence y

⊆ p. which is a

.

.

.

.

contradiction.

.

j

.

j

This construction can be used to obtain one more important result.

THEOREM 1.26 (Blok 1986)

,

Every unionffisplitting

has

im5

K

.

.

mediate predecessors in

. where

is the number of frames in

which

NExt

K

.

F

7 !

are not reducts of generated subframes of other frames in

: Every consis5

F

tent logic difierent from unionffisplittings has

immediate predecessors in

3

"

.

F

NExt

NExt

: ?

has 0 immediate predecessors in

:"

K

For

K

ADVANCED MODAL LOGIC

—5

Proof

The former claim follows from Theorem 1.13. To establish the

latter. we continue the proof of Theorem 1.27. One can show that L is

finitely axiomatizable over L

(the proof is rather technical. and we omit it

I

here). Then. by Zorn's Lemma. NExtL

contains an immediate predecessor

I

L

of L. Besides. L

L

⊆ L whenever I

⊆ J . Indeed.

.

I

I

J

"

L

L

⊆ (L

Log

)

(L

Log

) ⊆ L

(Log

Log

)

I

J

I

J

I

J

F

F

F

F

"

0

"

0

0

"

and if i

I

J then. for every ?

L and a sufficiently big l.

?

[

?

l

k

,

)

.

i

?

Log

"

)

.

Log

"

I

J

F

F

i

-

.

?

-

?

k

"

5.

from which ?

Log

Log

and so L

Log

Log

. It follows that

I

J

I

J

F

F

F

F

L

⊆ L

whenever I

⊆ J .

.

.

I

J

?

"

ff

"

.

It is worth noting that tabular logics. proper extensions of

and ex-

D

tensions of

are not union-splittings in NExt

. Similar results hold for

K,

K

the lattices NExt

and NExt

. where every consistent logic has degree of

D

T

incompleteness 3

(see [Blok 1986. 1960b]). It would be of interest to de-

"

.

scribe the behavior of this function in NExt

. NExt

. NExt

(where

K,

S,

Grz

Theorem 1.25 does not hold and where every tabular logic has finitely many

immediate predecessors) and other lattices of logics to be considered later

in this chapter.

.,5 Stronger forms of Kripke completeness

In the two preceding sections we were considering the problem of charac-

terizing

L

NExt

by classes of Kripke frames. The same problem

logics

K

arises in connection with the two consequence relations

and

as well.

?

L

.

L

"

"

Theorem 1.19 shows the way of introducing the corresponding concepts of

completeness.

With each Kripke frame

let us associate a consequence relation

⊆F by

F

putting. for any formula . and any set Φ of formulas. Φ

⊆F . iff (

" x)

⊆ Φ

j

M

implies (

" x)

⊆ . for every model

based on

and every point x in

.

M

M

F

F

j

j

Clearly. a modal logic L is Kripke complete iff. for any

set of formulas

.nite

j

Φ and any formula . Φ

. only if there is a Kripke frame

for L such

F

L

'"

ff

that Φ

⊆F . Now. let us call L

if this implication

strongly Kripke complete

holds for arbitrary sets Φ. In other words. L is strongly complete if every L-

'j

consistent set of formulas holds at some point in a model based on a Kripke

frame for L. Another reformulation: L is strongly complete iff L is Kripke

'

Fine "5'?(c" calls such logics compact- which does not agree with the use of this term

by Thomason "5'?ff"8

'
'
'
—ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

complete and the relation

⊆F :

is a Kripke frame for L

is finitary. It

F

follows from the construction of the canonical models that every canonical

T

fj

g

(in particular.

!persistent) logic is strongly complete. which provides us

with many examples of such logics in NExt

.

K

D

By Theorem 1.22. all logics characterized by first order definable classes

of Kripke frames are strongly complete. The converse does not hold: there

exist strongly complete logics which are not canonical. The simplest is the

bimodal logic of the frame

" 5" "

4 see Example 3.29 below. By applying

R

the Thomason simulation (to be introduced in Section 3.2) to this logic

h

i

we obtain a logic in NExt

with the same properties4 see Theorem 3.16.

K

Moreover. in contrast to

!persistence. strong Kripke completeness is not

preserved under finite sums of logics (see [Wolter 1996c]).

It is an open

D

problem. however. whether such logics exist in NExt

.

K,

Perhaps the simplest examples of Kripke complete logics which are not

strongly complete are

and

(use Theorem 1.76 and the fact that

GL

Grz

these logics are not elementary4 see

).

It is much

Correspondence Theory

more difficult to prove that the McKinsey logic

p

p is not

K

.,

,.

strongly complete4 the proof can be found in [Wang 1993]. For other ex-

"

.

amples of modal logics that are not strongly complete see Section 2.5. It

is worth noting also that. as was shown in [Fine 1985c]. every finite width

logic in a

.nite

language turns out to be strongly Kripke complete. though

this is not the case for logics in an infinite language. witness

GL

5

GL

.

⊆

(

p

q)

(

q

p).

.

.

.

.

"

"

"

.

,

.

For the consequence relation

. we should take the "global" version

⊆

.

L

.

F

of

⊆F . Namely. we put Φ

⊆

. if

⊆ Φ implies

⊆ . for any model

M

M

M

.

F

"

j

j

j

j

j

based on

. A modal logic L is called

if for any

global ly Kripke complete

F

finite set of formulas Φ and any formula . Φ

. only if there is a frame

.

L

'"

F

for L such that Φ

⊆

. L is

if this holds for

strongly global ly complete

.

F

'j

arbitrary (not only finite) Φ. We also say that L has the

global .nite model

property

if for every finite Φ and every . Φ

. only if there is a finite

.

L

'"

frame

for L such that Φ

⊆

.

F

.

F

'j

The global finite model property (FMP. for short) of many standard logics

can be proved by filtration. Say that a logic L

if for

strongly admits .ltration

every generated submodel

of the canonical model

and every finite set

L

M

M

of formulas # closed under subformulas. there is a filtration of

through

M

# based on a frame for L.

PROPOSITION 1.28 (Goranko and Passy 1993)

L

If

strongly admits .ltra5

tion then

L

has global FMP:

Proof

Suppose that Φ

. Φ finite. Then

Φ

. and so the

.

L

L

.,

.

set   ⊆

Φ

.

is L-consistent.

It remains to ,ltrate through

V

.,

'"

'"

.

6 f-

g

V

ADVANCED MODAL LOGIC

——

Sub

Sub

M

Φ

. the submodel of

generated by a maximal L-consistent

L

6

set containing  .

.

It follows in particular that

.

.

.

have global FMP.

K

T

D

KB

PROPOSITION 1.26

L

Suppose

is global ly complete ?has global FMP" and

Φ

L

Φ

is a .nite set of variable free formulas: Then

is global ly complete

?has global FMP" as wel l:

"

Proof

.

Let L

⊆ L

Φ and

.   finite. Then Φ

. and so

.

.

L

.

L

there exists a (finite) Kripke frame

for L such that Φ

⊆

. Since Φ

F

"

'"

6

'"

.

G

6

'j

contains no variables.

⊆ L

.

.

F

.

j

For n-transitive logics L the global consequence relation

is reducible to

.

L

"

the "local"

and so L is Kripke complete (has FMP. is strongly complete)

L

"

iff L is globally complete (has global FMP. is strongly globally complete). In

general the global properties are stronger than the "local" ones. Although

L is globally complete (has global FMP) only if L is complete (has FMP).

the converse does not hold (see [Wolter 1995a] and [Kracht 1996]).

EXAMPLE 1.29 Let L ⊆

p

p

(

p

p)

(

q

q). A

Alt

:

.,

.

,

,

Kripke frame

validates L iff no point in

has more than three successors.

F

F

"

.

"

. -

. -

.

-

F

is symmetric. and irreflexive points in it have at most one successor. By

Proposition 1.33. L is Kripke complete. The class of Kripke frames for L is

closed under (not necessarily generated) subframes. So. by Proposition 1.79

to be proved below. L has FMP. We show now that it does not have global

FMP. To this end we require the formulas:

—

⊆ q

q

q

" —

⊆

q

q

q

" —

⊆

q

q

q

"

.

.

,

:

,

.

,

:

:

.

,

:

. -

. -

-

.

. -

-

. -

.

. ⊆

p

p

—

" : ⊆

—

—

: i ⊆ 1" 3

—

—

.

.

".

:

.

i

i

.

,

,

. -

.

f

.

g .

.

.

Let

⊆

W" R

. where W ⊆ ' and

F

h

i

R ⊆

m" m

: m " 0

m" m " 1

: m 5 '

m" m

1

: m " 0

.

fh

i

g 6 fh

i

g 6 fh

[

i

g

We then have :

⊆

. In fact. . is true at 0 and : is true everywhere

.

F

'j

-

under the valuation

defined by

(p) ⊆ W

0

and

(q

) ⊆

2n " i :

i

V

V

V

n 5 '

. Clearly.

⊆ L and so :

. Suppose now that (

" x

)

⊆ .

F

N

.

L

.

[ f

g

f

and

⊆ : . for a model

based on a Kripke frame

⊆

V " S

for L. Then

N

N

G

g

j

'"

-

j

j

h

i

we can find a sequence x

. j 5 ' . such that x

S x

and x

⊆ —

. for

j

j

j

j

i

i

".

:

"

".

j 5 ' and i ⊆ 1" 3" 2. The reader can verify that all points x

are distinct.

j

j

Let us consider now the algebraic meaning of the notions introduced

above. A logic L is Kripke complete iff the variety AlgL of modal algebras

—(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

for L is generated by the class KrL ⊆

:

is a Kripke frame for L

. By

"

F

F

Birkhoff 's Theorem (see e.g. [Mal'cev 1982]). this means that

f

g

AlgL ⊆

KrL"

HSP

(i.e. AlgL is obtained by taking the closure of KrL under direct prod-

ucts. then the closure of the result under (isomorphic copies of ) subalgebras

and finally under homomorphic images). Clearly. L is globally complete iff

precisely the same quasi-identities hold in KrL and AlgL. And since the

quasi-variety generated by a class of algebras

is

(where

denotes

SPP

U

P

U

the closure under ultraproducts4 see [Mal'cev 1982]). L is globally complete

C

C

iff

AlgL ⊆

KrL.

SPP

U

Goldblatt [1969] calls the variety AlgL

if AlgL ⊆

KrL. or. equiv-

complex

S

alently. if AlgL ⊆

KrL (this follows from the fact that the dual of the

SP

disjoint union of a family of Kripke frames

: i

I

is isomorphic to the

i

F

product

). We say a logic L is

-

.

a cardinal. if every

F

.

.

complex

"

f

?

g

i

I

i

:

modal algebra for L with

generators is a subalgebra of

for some

.

Q

"

F

Kripke frame

⊆ L. As was shown in [Wolter 1992]. this notion turns

F

7

out to be the algebraic counterpart of both strong completeness and strong

j

global completeness of logics in

with

variables.

in.nite languages

.

THEOREM 1.50

L

For every normal modal logic

in an in.nite language

with

variables the fol lowing conditions are equivalent"

.

(i) L

is strongly Kripke complete'

(ii) L

is global ly strongly complete'

(iii) L

is

5complex:

.

Proof

A

.

(i)

(iii) Suppose the cardinality of

AlgL does not exceed

.

Denote by

the algebra of modal formulas over

propositional variables

L

.

8

?

and take some homomorphism h from

onto

. For each ultrafilter

in

L

A

A

. the set h

(

) is maximal L-consistent. Since L is strongly complete.

.

r

5

r

there is a model

⊆

"

with root x

based on a Kripke frame

M

F

V

F

M

for L and such that (

" x

)

⊆ h

(

). Without loss of generality we

5

r

r

r

r

h

i

.

r

r

r

j

r

may assume that the frames

for distinct

are disjoint. Let

be the

F

F

disjoint union of all of them. Define a homomorphism

from

into

by

V

L

F

r

r

"

taking

V

V

A

(p) ⊆

(p) :

is an ultrafilter in

.

f

r

g

r

5

"

Then

(

) is a subalgebra of

AlgL isomorphic to

.

V

L

F

A

The implication (iii)

(ii) is trivial. To prove (ii)

(i). consider an

?

L-consistent set of formulas Φ of cardinality

and put

.

8

8

n

.

7

  ⊆

p

(p

.) : n 5 ' " .

Φ

"

f

g 6 f

.

?

g

ADVANCED MODAL LOGIC

—)

where the variable p does not occur in formulas from Φ. It is easily checked

that all finite subsets of   are L-consistent. so   is L-consistent too. It

follows that

p

. : .

Φ

p. And since L is globally strongly

.

L

complete. there exists a model

based on a Kripke frame for L such that

M

f

.

?

g '"

-

M

M

M

⊆

p

. : .

Φ

and (

" x)

⊆ p. for some x. But then (

" x)

⊆ Φ.

j

f

.

?

g

j

j

.

.,' Canonical formulas

The main problem of completeness theory in modal logic is not only to find

a sufficiently simple class of frames with respect to which a given logic L is

complete but also to characterize the constitution of frames for L (in this

class). The first order approach to the characterization problem. discussed

in Section 1.2 in connection with Sahlqvist's Theorem. comes across two

obstacles. First. there are formulas whose Kripke frames cannot be de-

scribed in the first order language with R and ⊆. The best known example

is probably the

L-ob axiom

la

⊆

(

p

p)

p.

.

.

.

.

.

F

F

la

⊆

iff

is transitive. irreflexive (i.e. a strict partial order) and

Noethe5

j

rian

in the sense that it contains no infinite ascending chain of distinct

points. And as is well known. the condition of Noetherianness is not a first

order one. The second obstacle is that this approach deals only with log-

ics that are Kripke complete4 it does not take into account sets of possible

values.

There is another. purely frame-theoretic method of characterizing the

structure of frames. For instance. a frame

validates

,

iff

does

G

F

G

K

not contain a generated subframe reducible to

.

It was shown in [Za-

F

kharyaschev 1965. 1966. 1993] that in a similar manner one can describe

transitive

frames validating an arbitrary modal formula.

It is not clear

whether characterizations of this sort can be extended to the class of all

frames (an important step in this direction would be a generalization to

n-transitive frames). That is why all frames in this section are assumed to

be transitive. First we illustrate this method by a simple example.

EXAMPLE 1.51 Suppose a frame

⊆

W" R" P

refutes

under some

F

la

valuation. Then the set V ⊆

x

W : x

⊆

is in P and V

V

. It

la

h

i

follows from the former that

⊆

V " R

V "

X

V : X

P

is a frame—

G

.

f

?

'j

g

ff

;

we call it the

V . And the latter condition means

subframe of

induced by

F

h

f

0

?

gi

that

is reducible to the single reflexive point

which is the simplest

G

refutation frame for

. Moreover. one can readily check that the converse

la

o

also holds: if there is a subframe

of

reducible to

then

⊆

.

G

F

F

la

o

'j

—0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

This example motivates the following definitions. Given frames

⊆

F

W" R" P

and

⊆

V " S" Q

. a partial (i.e. not completely defined. in

G

h

i

h

i

general) map f from W onto V is called a

of

to

if it

subreduction

F

G

satisfies the reduction conditions (R1)!(R2) for all x and y in the domain

of f and all X

Q. The domain of f will be denoted by domf . In other

words. an f -subreduct of

is a reduct of the subframe of

induced by

F

F

?

domf . A frame

⊆

V " S" Q

is a

subframe

of

⊆

W" R" P

if V

W and

G

F

the identity map on V is a subreduction of

to

. i.e. if S ⊆ R

V and

F

G

.

h

i

h

i

ff

Q

P . Note that a generated subframe

of

is not in general a subframe

G

F

ff

F

of

. since V may be not in P .

Thus. the result of Example 1.51 can be reformulated like this:

⊆

F

la

iff

is subreducible to

.

F

'j

A subreduction f of

to

is called

if

co.nal

o

F

G

domf

domf

.

3 ff

;

This important notion can be motivated by the following observation:

F

refutes

iff

is cofinally subreducible to

(a plain subreduction is not

,

F

enough).

]

5

THEOREM 1.53

Every refutation frame

⊆

W" R" P

.(p

" . . . " p

)

for

is

.

n

F

co.nal ly subreducible to a .nite rooted refutation frame for

containing at

.

h

i

most

points:

c

⊆ 3

(c

(1) " . . . " c

(3

))

5

n

n

j

j

n

5

-

Sub

6

Proof

F

V

Suppose . is refuted in

under a valuation

. Without loss

of generality we can assume

to be generated by

(p

)" . . . "

(p

). Let

.

n

F

V

V

X

" . . . " X

be all distinct maximal 0-cyclic sets in

. Clearly. m

c

(1)

.

m

n

F

but unlike Theorem 1.6.

is not in general refined and so these sets are

F

7

not necessarily clusters of depth 1. However. they can be easily reduced

to such clusters. Define an equivalence relation

on W by putting x

y

iff x ⊆ y or x" y

X

. for some i

1" . . . " m

. and x

y (as before

i

?

2

2

# ⊆

p

" . . . " p

). Let [x] be the equivalence class under

generated by

.

n

?

? f

g

2

f

g

2

x and [X ] ⊆

[x] : x

X

. for X

P . By the definition of cyclic sets.

xRy iff [x]

[y ]

. So the map x

[x] is a reduction of

to the frame

F

f

?

g

?

F

F

.

.

.

.

i

⊆

W

" R

" P

which results from

by "folding up" the 0-cyclic sets X

ff

;

".

.

.

.

.

h

i

into clusters of depth 1 and leaving the other points untouched: W

⊆ [W ].

.

.

[x]R

[y ] iff [x]

[y ]

and P

⊆

[X ] : X

P

. (Roughly. we refine that

.

.

.

.

part of

which gives points of depth 1.) Put

(p

) ⊆ [

(p

)]. Then by

F

V

V

.

i

i

.

ff

;

f

?

g

the Reduction (or P-morphism) Theorem. we have x

⊆ : iff [x]

⊆ : . for

j

j

every :

.

Sub

?

Let X be the set of all points in

of depth " 1 having

.-equivalent

F

Sub

.

.

successors of depth 1.

It is not hard to see that X

P

. Denote by

.

.

?

?

The function

]

7 was de:ned in Section 58ff8

c

m

n

ADVANCED MODAL LOGIC

—?

F

F

V

.

.

.

.

.

.

.

.

.

⊆

W

" R

" P

the subframe of

induced by W

X and let

be the

h

i

[

restriction of

to

. By induction on the construction of :

. one

V

F

Sub

.

.

.

can readily show that : has the same truth-values at common points in

F

.

.

?

and

(under

and

. respectively) and so

⊆ . The partial map

F

V

V

F

.

.

.

.

.

x

[x]. for [x]

W

. is a cofinal subreduction of

to

.

.

.

'j

F

F

".

?

Then we take the maximal 1-cyclic sets in

. "fold" them up into clusters

.

F

of depth 3 and remove those points of depth " 3 that have

.-equivalent

Sub

successors of depth 3. The resulting frame

will be a cofinal subreduct of

,

F

F

F

.

and so of

as well. After that we form clusters of depth 2. and so forth.

In at most 3

steps of that sort we shall construct a cofinal subreduct

j

j

Sub

5

of

refuting . and containing

c

points.

It remains to select in it a

5

F

suitable rooted generated subframe.

.

7

For the ma jority of standard modal axioms the converse also holds.

However. not for all. The simplest counterexample is the density axiom

den

.

.

H

⊆

p

p. It is refuted by the chain

of two irreflexive points but

becomes valid if we insert between them a reflexive one. In fact.

⊆

F

den

.

iff there is a subreduction f of

to

such that f (x

) ⊆

a

. for no point

F

H

'j

x in domf

domf . where a is the final point in

.

3

f

g

H

Loosely. every refutation frame for formulas like

can be constructed by

la

3 [

adding new points to a frame

that is reducible to some finite refutation

G

frame of fixed size. For formulas like

we have to take into account the

,

cofinality condition and do not put new points "above"

. And formulas

G

]

like

impose another restriction: some places inside

may be "closed"

den

G

for inserting new points. These "closed domains" can be singled out in the

following way.

Suppose

⊆

"

is a model and

an antichain in

. Say that

is

N

H

U

a

H

a

an

in

relative to a formula . if there is a pair ta ⊆ (Φa "  a )

open domain

h

i

N

such that Φa

 a ⊆

.

Φa

 a

and

Sub

K,

6

.

'?

.

:

Φa implies :

Φa .

V

W

5

?

?

.

.

:

Φa iff a

⊆

: for all a

.

a

"

5

?

j

?

Otherwise

is called a

in

relative to . A reflexive singleton

closed domain

a

N

a

⊆

a

is always open: just take ta ⊆ (

:

. : a

⊆ :

"

:

. :

Sub

Sub

f

g

f

?

j

g

f

?

a

⊆ :

). It is easy to see also that antichains consisting of points from the

'j

g

same clusters are open or closed simultaneously4 we shall not distinguish

between such antichains.

For a frame

and a (possibly empty) set

of antichains in

. we say a

H

D

H

subreduction f of

to

satisfies the

for

if

closed domain condition

F

H

D

(CDC)

x

domf

domf

f (x

) ⊆

.

d

D

d

-1

?

3 [

1

?

3

3

Notice that the cofinal subreduction f of

to the resulting finite rooted

F

frame

in the proof of Theorem 1.53 satisfies (CDC) for the set

of

H

D

—fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

closed domains in the corresponding model

on

refuting .

Indeed.

N

H

every x

domf

domf has a

.-equivalent successor y

domf .

Sub

and so an antichain

such that f (x

) ⊆

is open. since we can take

d

d

?

3 [

?

td ⊆ (

:

. : y

⊆ :

"

:

. : y

⊆ :

). On the other hand. we

Sub

Sub

3

3

f

?

j

g

f

?

'j

g

have

PROPOSITION 1.52

⊆

"

.

Suppose

is a .nite countermodel for

N

H

U

and

the set of al l closed domains in

relative to

: Then

.

⊆ .

D

N

F

h

i

whenever there is a co.nal subreduction

of

to

satisfying ?CDC" for

f

F

H

'j

D

: Moreover. if

.

is negation free ?i:e:. contains no

.

.

" then a plain

,

subreduction satisfying ?CDC" for

is enough:

D

:

-

Proof

F

If f is cofinal and

⊆

W" R" P

then we can assume domf

⊆ W .

Define a valuation

in

as follows. If x

domf then we take x

⊆ p iff

V

F

h

i

3

f (x)

⊆ p. for every variable p in . If x

domf then f (x

)

⊆

. since f is

?

j

j

'?

3

fl

cofinal. Let

be an antichain in

such that

⊆ f (x

). By (CDC).

is

a

H

a

a

an open domain in

. and we put y

⊆ p iff p

Φa . for every y

domf such

N

3

3

that f (y

) ⊆ f (x

). One can show that

is really a valuation in

and.

V

F

j

?

'?

for every :

. x

⊆ : iff f (x)

⊆ : in the case x

domf . and x

⊆ :

Sub

3

3

iff :

Φa . where

is the open domain in

associated with x. in the case

a

N

?

j

j

?

j

?

x

domf .

'?

If . is negation free and f is a plain subreduction then f (x

) may be

empty. In such a case we just put x

⊆ p. for all variables p.

j

3

.

Now let us summarize what we have got. Given an arbitrary formula

. we can effectively construct a finite collection of finite rooted frames

F

F

.

n

5

" . . . "

(underlying all possible rooted countermodels for . with

c

points) and select in them sets

" . . . "

of antichains (open domains in

.

n

D

D

7

those countermodels) such that. for any frame

.

⊆ . iff there is a cofinal

F

F

subreduction of

to

. for some i. satisfying (CDC) for

. If . is negation

i

i

F

F

D

'j

free then a plain subreduction satisfying (CDC) is enough.

This general characterization of the constitution of refutation transitive

frames can be presented in a more convenient form if with every finite rooted

frame

⊆

W" R

and a set

of antichains in

we associate formulas

F

D

F

—(

"

"

) and —(

"

) such that

⊆ —(

"

"

) (

⊆ —(

"

)) iff there is

F

D

F

D

G

F

D

G

F

D

h

i

a cofinal (respectively. plain) subreduction of

to

satisfying (CDC) for

G

F

:

'j

:

'j

D

. For instance. one can take

n

—(

"

"

) ⊆

.

ij

.

i

.d

.

p

.

F

D

:

.

.

.

.

1

a

Ra

i

5.

d

D

i

.

j

.

.

:

where a

" . . . " a

are all points in

and a

is its root.

.

n

.

F

.

⊆

(

p

p

)"

ij

j

i

"

.

.

.

'
ADVANCED MODAL LOGIC

—'

n

.

⊆

((

i

p

k

p

p

)

p

"

j

i

i

"

.

.

a

Ra

j

:j

i

.

i

k

5.

5

.

.

.

.

9

"

n

.d ⊆

(

p

j

p

i

p

)"

j

.

.

.

a

W

i

.

d

i

5.

.

a

d

j

"

.

.

:

5

8

:

n

"

"

.

.

.

⊆

(

p

i

).

1

. :

i

5.

.

—(

"

) results from —(

"

"

) by deleting the conjunct .

. —(

"

"

) and

F

D

F

D

F

D

—(

"

) are called the

and

for

canonical

negation free canonical formulas

F

D

F

:

:

1

and

. respectively. It is not hard to check that if —(

"

"

) is refuted in

D

F

D

G

⊆

V " S" Q

under some valuation then the partial map defined by x

a

i

:

h

i

".

if the premise of —(

"

"

) is true at x and p

false is a cofinal subreduction

i

F

D

of

to

satisfying (CDC) for

4 and conversely. if f is such a subreduction

G

F

D

:

then the valuation

defined by

(p

) ⊆ V

f

(a

) refutes —(

"

"

) at

i

5

i

U

U

F

D

.

any point in f

(a

).

5

.

.

[

:

THEOREM 1.55

.

There is an algorithm which. given a formula

. returns

canonical formulas

—(

"

"

)" . . . " —(

"

"

)

such that

.

.

n

n

F

D

F

D

:

:

K,

K,

F

D

F

D

. ⊆

—(

"

"

)

. . .

—(

"

"

).

.

.

n

n

"

"

:

"

"

:

So the set of canonical formulas is complete for the class

NExt

: If

is

.

K,

negation free then one can use negation free canonical formulas:

It is not hard to see that

. is a splitting of NExt

iff . is deduc-

K,

K,

tively equivalent in NExt

to a formula of the form —(

"

"

). where

K,

F

D

D

"

'

'

is the set of all antichains in

(in this case

,

⊆

—(

"

"

)). Such

F

F

F

D

K,

K,

:

'

formulas are known as

(Jankov [1962] introduced them for

Jankov formulas

"

:

intuitionistic logic). or

(cf.

[Fine 1985a]). or

frame formulas

Jankov9Fine

formulas

. Since

is not a union-splitting of NExt

. this class of logics

GL

K,

has no axiomatic basis.

We conclude this section by showing in Table 3 canonical axiomatizations

of some standard modal logics in the field of

. For brevity we write

K,

—(

"

) instead of —(

"

"

) and —

(

"

) instead of —(

"

"

). Each

in

F

F

F

F

D

'

'

:

fl

:

:

:

the table is to be replaced by both

and

.

For more information about the canonical formulas the reader is referred

o

5

to [Zakharyaschev 1993. 1998b].

.,? Decidability via the "nite model property

Although. for cardinality reason. there are "much more" undecidable logics

than decidable ones. almost all "natural" propositional systems close to

"

([

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

D,

K,

⊆

—(

"

)

S,

K,

⊆

—(

)

"

5

:

GL

K,

⊆

—(

)

"

5

"

o

Grz

K,

⊆

—(

)

—(

)

"

5

"

.

.

o o

K,

:

K,

.

⊆

—(

"

)

—(

"

)

"

5

:

"

:

,

:

.

.

o o

Triv

K,

⊆

—(

)

—(

)

—(

)

"

5

"

"

o

.

.

o o

,

:

o

"

Verum

K,

⊆

—(

)

—(

)

"

o

"

5

,

:

5

"

S.

S,

⊆

—(

)

o

"

"

o

"

KfiB

K,

⊆

—(

) (5 axioms)

"

1

3

5

5

AK

.—

A

.

A

GL

⊆

—(

"

1

"

1" 3

)

.

"

5

ff

g

f

gg

K,

"

K,

.

⊆

—(

"

)

—(

"

)

—(

"

) (6 axioms)

"

5

:

"

o

:

"

:

5

"

5

5

A

.

"

"

AK

.—

K,

5

K,

.

⊆

—(

) (6 axioms)

AK

.—

A

.

"

.

.

o o

o

.—

AK

A

.

,

:

o

"

Dum

S,

⊆

—(

)

—(

)

"

o

"

n

".

.

.

o o

,

:

KfiBW

K,

n

⊆

—(

) (3n " 5 axioms)

  6 6 6

'I

"(

'

"

z '? "

"

n

.

"

.

.

1

KfiBD

K,

n

⊆

—(

0

) (3

axioms)

"

n

".

"

m

5

.

"

.

.

1

5

"

'

K,

K,

n:m

⊆

—(

0

"

)

D

"

5

Table 3. Canonical axioms of standard modal logics

ADVANCED MODAL LOGIC

(5

those we deal with in this chapter turn out to be decidable. Relevant and

linear logics are probably the best known among very few exceptions (see

[Urquhart 1965]. [Lincoln

1993]).

et al:

The ma jority of decidability results in modal logic was obtained by means

of establishing the finite model property. FMP by itself does not ensure yet

decidability (there is a continuum of logics with FMP)4 some additional con-

ditions are required to be satisfied. For instance. to prove the decidability

of

McKinsey [1951] used two such conditions: that the logic under con-

S,

sideration is characterized by an effective class of finite frames (or algebras.

matrices. models. etc.) and that there is an effective (exponential in the case

of

) upper bound for the size of minimal refutation frames. Under these

S,

conditions. a formula belongs to the logic iff it is validated by (finite) frames

in a finite family which can be effectively constructed. Another sufficient

condition of decidability is provided by the following well known

THEOREM 1.57 (Harrop 1976)

Every .nitely axiomatizable logic with FMP

is decidable:

Here we need not to know a priori anything about the structure of frames

for a given logic. This information is replaced by checking the validity of its

axioms in finite frames. and the restriction of the size of refutation frames

is replaced by constructing all possible derivations:

in a finite number of

steps we either separate a tested formula from the logic or derive it. Note

that unlike the previous case now we cannot estimate the time required to

complete this algorithm.

The condition of finite axiomatizability in Harrop's Theorem cannot be

weakened to that of recursive axiomatizability. For there is a logic of depth

2 in NExt

(i.e. a logic in NExt

) with an infinite set of inde-

K,

KfiBD

:

pendent axioms4 so the logic of depth 2 axiomatizable by some recursively

enumerable but not recursive sequence of formulas in this set is undecid-

able and has FMP. On the other hand there are examples of undecidable

logics characterized by decidable classes of finite frames (see e.g. [Chagrov

and Zakharyaschev 1998]). Yet one can generalize Harrop's Theorem in

the following way. A logic is decidable iff it is recursively enumerable and

characterized by a recursive class of recursive algebras. However. this cri-

terion is absolutely useless in its generality. In this connection we note two

open problems posed by Kuznetsov [1989]. Is every finitely axiomatizable

logic characterized by recursive algebras? Is every finitely axiomatizable

logic. characterized by recursive algebras. decidable? (That

axiom-

.nite

atizability is essential here is explained by the following fact:

if a lattice

of logics contains a logic with a continuum of immediate predecessors then

there is no countable sequence of algebras such that every logic in the lattice

is characterized by one of its subsequences. For details see [Chagrov and

Zakharyaschev 1998].)

(ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

FMP of almost all standard systems was proved using various forms of

filtration (consult Section 13

and [Gabbay 1986]). How-

Basic Modal Logic

ever. the method of filtration is rather capricious4 one needs a special craft

to apply it in each particular case (for instance. to find a suitable "filter").

In this and two subsequent sections we discuss other methods of proving

FMP which are applicable to families of logics and provide in fact sufficient

conditions of FMP. (It is to be noted that the families of Kripke complete

logics considered in Section 1.2 contain logics without FMP.) A pair of such

conditions was already presented in

Basic Modal Logic

:

THEOREM 1.56 (Segerberg 1981)

NExt

Each logic in

characterized by

K,

a frame of .nite depth ?or. which is equivalent. containing

. for

KfiBD

n

some

" has FMP:

n 5 '

THEOREM 1.58 (Bull 1966b. Fine 1981)

NExt

.

Each logic in

has FMP

S,

5

and is .nitely axiomatizable ?and so decidable":

The former result. covering a continuum of logics. follows immediately

from the description of finitely generated refined frames for

in Section 1.3

K,

and the latter is a consequence of Theorem 1.73 and Example 1.75 below.

It is worth noting also that since

(n) is finite for every logic L

NExt

L

F

K,

of finite depth and every n 5 ' . there are only finitely many pairwise non-

?

equivalent in L formulas of n variables. Logics with this property are called

local ly tabular

local ly .nite

(or

). Moreover. as was observed by Maksimova

[1987a]. the converse is also true: if L

NExt

has frames of any depth

K,

5 ' then the formulas in the sequence .

⊆ p. .

⊆ p

(p

.

)

.

".

n

n

?

.

.

are not equivalent in L. Thus. a logic in NExt

is locally tabular iff it

K,

,

.

is of finite depth. For L

NExt

this criterion can be reformulated in

S,

the following way: L is not locally tabular iff L

.

. where

.

⊆

Grz

5

Grz

5

?

S,

5

Grz

GL

GL

5

.

. Likewise. L

NExt

is not locally tabular iff L

.

.

ff

"

?

ff

Nagle and Thomason [1967] showed that all normal extensions of

are

K.

locally tabular.

Uniform logics

Fine [1987a] used a modal analog of the full disjunctive

normal form for constructing finite models and proving FMP of a family

of logics in NExt

(containing in particular the McKinsey system

D

K

.,

,.

p

p which had resisted all attempts to prove its completeness by

"

.

the method of canonical models and filtration). Let us notice first that every

formula .(p

" . . . " p

) is equivalent in

either to

or to a disjunction

K

.

m

of normal forms (in the variables p

" . . . " p

) of degree md(.). which are

.

m

:

defined inductively in the following way.

. the set of

normal forms of

NF

.

degree

0. contains all formulas of the form

p

. . .

p

. where each

.

.

m

m

-

.

. -

ADVANCED MODAL LOGIC

(—

i

n

".

is either blank or

.

. the set of

n " 1.

normal forms of degree

NF

-

-

consists of formulas of the form

fl

fl

. . .

fl

"

.

.

k

k

,

,

. -

.

. -

where fl

and fl

" . . . " fl

are all distinct normal forms in

. Put

.

.

k

n

NF

NF

NF

NF

NF

D

⊆

. Using the fact that

fl : fl

it is not

n

n

n.,

?

,

hard to see also that in

every formula . with md(.)

n is equivalent

D

S

W

f

?

g ?

either to

or to a disjunction of normal forms of degree n such that at

7

least one of

" . . . "

in the inductive step of the definition above is blank.

.

k

:

Such normal forms are called

-

.

D

suitable

-

-

It should be clear that. for any distinct fl

" fl

.

(fl

fl

)

.

.

.

.

.

n

NF

K

Consequently. for every fl

and every .(p

" . . . " p

) with md(.)

n.

NF

n

m

.

?

-

.

?

we have either fl

.

or fl

.

.

K

K

?

7

With each

-suitable normal form fl we associate a model

⊆

"

?

?

?

D

M

F

V

.

?

. -

?

on a frame

⊆

W

" R

by taking

?

?

?

F

h

i

h

i

n

W

⊆

?

fl

.

NF

.

: fl

5

fl" for some n

0

"

f]g 6 f

?

9

g

fl

.

5 fl

.

iff

fl

.

is a conjunct of fl

.

"

,

fl .R

fl . iff either fl . " fl . or md(fl . ) ⊆ 0 and fl . ⊆

"

?

]

V

?

?

.

(p) ⊆

fl .

W

: p is a conjunct of fl

.

f

?

g

According to the definition.

is the reflexive last point in

and so

is

?

?

F

F

serial. By a straightforward induction on the degree of fl

W

one can

.

?

]

readily show that (

" fl

)

⊆ fl

. It follows immediately that

has FMP.

?

.

.

M

?

D

Indeed. given .

. we reduce

. to a disjunction of

-suitable normal

D

D

j

forms with at least one disjunct fl. and then (

" fl)

⊆ fl.

?

M

'?

-

It turns out that in the same way we can prove FMP of all logics in

j

NExt

axiomatizable by

. which are defined as follows.

uniform formulas

D

Every . without modal operators is a

04 and if

uniform formula of degree

. ⊆ :(

?

" . . . "

?

). where

"

. md(:(p

" . . . " p

)) ⊆ 0 and

.

.

.

m

m

i

m

.

,

#

#

#

? f

g

?

" . . . " ?

are uniform formulas of degree n. then . is a

uniform formula

.

m

of degree

n " 1. A remarkable property of uniform formulas is the following

PROPOSITION 1.56

.

n

Suppose

is a uniform formula of degree

and

.

M

N

are models based upon the same frame and such that. for some point

x

.

M

N

(

" y)

⊆ p

(

" y)

⊆ p

y

x

p

.

i,

for every

and every variable

in

: Then

n

M

N

(

" x)

⊆ .

(

" x)

⊆ .

i,

:

j

j

?

3

j

j

Given a logic L. we call a normal form fl L-

if

⊆ L.

suitable

F

?

j

THEOREM 1.59 (Fine 1987a)

L

NExt

Every logic

axiomatizable by

D

uniform formulas has FMP:

?

((

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Proof

It suffices to prove that each formula . with md(.)

n is equiva-

lent in L either to

or to a disjunction of L-suitable normal forms of degree

7

n. And this fact will be established if we show that every

-suitable normal

D

:

form fl such that fl

L is L-suitable. Suppose otherwise. Let fl be an

L-consistent and

-suitable normal form of the least possible degree under

D

. : '?

which it is not L-suitable. Then there are a uniform formula :

L of some

degree m and a model

⊆

"

such that (

" fl)

⊆ : .

?

M

F

V

M

?

For every variable p in : . let Φ

⊆

fl

fl

: (

" fl

)

⊆ p

and let

p

.

.

M

h

i

m

'j

9

⊆

Φ

(if Φ

⊆

then 9

⊆

). Observe that for every fl

fl

we have

p

p

p

p

.

f

?

3

j

m

g

M

M

(

" fl

)

⊆ 9

iff fl

Φ

iff (

" fl

)

⊆ p. Therefore. by Proposition 1.56.

?

.

p

.

p

.

W

fl

:

?

3

the formula :

which results from : by replacing each p with 9

is false

.

p

j

?

j

at fl in

. Now. if md(:

) " n then m " n and so 9

⊆

for every p

?

.

p

M

in : . i.e. :

is variable free. But then :

is equivalent in

to

or

.

.

.

:

D

contrary to

⊆ :

and L being consistent. And if md(:

)

n then either

?

.

.

F

]

:

fl

:

. which is impossible. since (

" fl)

⊆ fl

:

. or fl

:

.

.

?

.

.

K

K

M

'j

7

.

?

'j

.

. -

?

from which :

fl

and so

fl

L. contrary to fl being L-consistent.

K

.

. -

?

-

?

.

Logics with

'axioms

Another result. connecting FMP of logics with

.,

the distribution of

and

over their axioms. is based on the following

.

,

LEMMA 1.70

.

For any

and

:

.

.

:

.

:

S.

i,

K,

:

,

,

.,

.,

5

?

5

?

Proof

K,

Suppose

.

:

. Then there is a finite model

.

M

.,

.,

based on a transitive frame. and a point x in it such that x

⊆

. and

.

'?

.,

x

⊆

: .

It follows from the former that every final cluster accessible

.,

j

'j

from x. if any. is non-degenerate and contains a point where . is true. The

latter means that x sees a final cluster C at all points of which : is false.

Now. taking the generated submodel of

based on C . we obtain a model

M

for

refuting

.

: . The rest is obvious. since

p

p is in

S.

S.

,

,

,

,.

.

5

.

and

.

K,

S.

ff

Formulas in which every occurrence of a variable is in the scope of a

modality

will be called

-

.

formulas

.,

.,

THEOREM 1.71 (Rybakov 1986)

L

NExt

If a logic

is decidable ?or

K,

has FMP" and

is a

5formula then

is also decidable ?has FMP":

:

L

:

.,

?

"

Proof

Let : ⊆ :

(

?

" . . . "

?

). for some formula :

(q

" . . . " q

). If

.

.

n

n

.

.

.,

.,

.(p

" . . . " p

)

L

: then there exists a derivation of . in L

: in which

.

m

substitution instances of : contain no variables different from p

" . . . " p

.

.

m

?

"

"

Each of these instances has the form :

(

?

" . . . "

?

). where every ?

is

.

.

.

.

n

.

i

.,

.,

some substitution instance of ?

containing only p

" . . . " p

. By Lemma 1.70

i

m

.

and in view of the local tabularity of

(it is of depth 1). there are finitely

S.

ADVANCED MODAL LOGIC

()

many pairwise non-equivalent in

substitution instances of

?

of that

i

K,

.,

sort (the reader can easily estimate the number of them). So there exist

only finitely many pairwise non-equivalent in

substitution instances of

K,

: containing p

" . . . " p

. say :

" . . . " :

. and we can effectively construct

.

.

m

k

them. Then. by the Deduction Theorem.

.

L

: iff :

" . . . " :

.

. iff

(:

. . .

:

)

.

L

.

.

k

k

L

"

.

?

"

"

.

.

.

?

and so L

: is decidable (or has FMP) whenever L is decidable (has FMP).

"

.

.,

It should be noted that by adding to L with FMP infinitely many

-

formulas we can construct an incomplete logic. For a concrete example see

[Rybakov 1988]. By adding a variable free formula to a logic in NExt

with

K

FMP one can get a logic without FMP. However.

. . variable free.

K

has FMP. as can be easily shown by the standard filtration through the set

"

Sub

Sub

K

.

: . where :

. Infinitely many variable free formulas can

6

'?

"

axiomatize a normal extension of

without FMP (for a concrete example

K,

see [Chagrov and Zakharyaschev 1998]).

.,1 Subframe and co"nal subframe logics

A very useful source of information for investigating various properties of

logics in NExt

is their canonical axioms. Notice. for instance. that the

K,

canonical axioms of all logics in Table 3. save

and

. contain no

.

n:m

A

K,

closed domains. Canonical and negation free canonical formulas of the form

—(

) and —(

"

) are called

and

. respec-

subframe

co.nal subframe formulas

F

F

tively. and logics in NExt

axiomatizable by them are called

and

subframe

K,

:

co.nal subframe logics

. The classes of such logics will be denoted by

and

. Subframe and cofinal subframe logics in NExt

were studied

K,

S F

C SF

by Fine [1967] and Zakharyaschev [1965. 1966. 1996].

THEOREM 1.73

Al l logics in

and

have FMP:

SF

CSF

Proof

K,

F

Suppose L ⊆

—(

"

) : i

I

and .

L. By Theorem 1.55.

i

without loss of generality we may assume that . is a canonical formula.

" f

:

?

g

'?

say. —(

"

"

). Now consider two cases. (1) For no i

I .

is cofinally

F

D

F

subreducible to

. Then

⊆ L.

⊆ —(

"

"

). and we are done. (3)

i

F

F

F

F

D

F

:

?

is cofinally subreducible to —(

"

). for some i

I . In this case we have

i

F

j

'j

:

—(

"

"

)

—(

"

)

L. which is a contradiction. Indeed. suppose

i

F

D

F

K,

:

?

G

F

D

G

F

⊆ —(

"

"

). Then there is a cofinal subreduction of

to

. And since

:

?

"

:

ff

'j

:

the composition of (cofinal) subreductions is again a (cofinal) subreduction.

G

F

G

F

is cofinally subreducible to

. which means that

⊆ —(

"

). Subframe

i

i

logics are treated analogously.

'j

:

.

(0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

The names "subframe logic" and "cofinal subframe logic" are explained

by the following frame-theoretic characterization of these logics. A subframe

G

F

F

⊆

V " S" Q

of a frame

is called

if V

V

in

. Say that a class

co.nal

h

i

3 ff

;

of frames is

if every (cofinal) subframe

closed under ?co.nal" subframes

C

of

is in

whenever

.

F

F

C

? C

THEOREM 1.72 L

NExt

is a ?co.nal" subframe logic i, it is charac5

K,

terized by a class of frames that is closed under ?co.nal" subframes:

?

Proof

Suppose L

. We show that the class of all frames for L is

closed under cofinal subframes. Let

⊆ L and

be a cofinal subframe

G

H

? CS F

of

.

If

⊆ —(

"

). for some —(

"

)

L. then (since

is cofinally

G

H

F

F

G

j

subreducible to

)

⊆ —(

"

). which is a contradiction. So

⊆ L.

H

G

F

H

'j

:

:

?

Now suppose that L is characterized by some class of frames

closed

'j

:

j

under cofinal subframes. We show that L ⊆ L

. where

.

C

L

.

⊆

K,

—(

"

) :

⊆ L

.

F

F

" f

:

'j

g

If

is a finite rooted frame and

⊆ L then —(

"

)

L. for otherwise

F

F

F

G

F

G

H

⊆ —(

"

) for some

. and hence there is a cofinal subframe

of

'j

:

?

'j

:

? C

G

F

H

which is reducible to

4 but

and so. by the Reduction Theorem.

F

is a frame for L. which is a contradiction. Thus. L

L. To prove the

? C

.

ff

converse. suppose —(

"

"

)

L. Then

⊆ L. and hence —(

"

)

L

.

.

F

D

F

F

:

?

'j

:

?

from which —(

"

"

)

L

.

.

F

D

:

?

Subframe logics are considered in the same way.

.

It follows in particular that

(

.

and

.

are cofinal

K,

:

K,

"

subframe logics but not subframe ones). One can easily show also that

S F — CSF

is a complete sublattice of NExt

and

a complete sublattice of

K,

CSF

SF

.

CSF

EXAMPLE 1.75 Every normal extension of

.

is axiomatizable by canon-

S,

5

ical formulas which are based on chains of non-degenerate clusters and so

have no closed domains. Therefore. NExt

.

.

S,

5

— C S F

The classes

and

contain a continuum of logics. And

yet. unlike NExt

or NExt

. their structure and their logics are not so

K

K,

SF

CS F [ SF

complex. For instance. it is not hard to see that every logic in

is

uniquely axiomatizable by an independent set of cofinal subframe formulas

CSF

and so these formulas form an axiomatic basis for

.

The concept of subframe logic was extended in [Wolter 1992] to the class

CSF

NExt

by taking the frame-theoretic characterization of Theorem 1.72 as

K

the definition. Namely. we say that L

NExt

is a

if the

subframe logic

K

class of frames for L is closed under subframes. In other words. subframe

?

ADVANCED MODAL LOGIC

(?

logics are precisely those logics whose axioms "do not force the existence of

points". For example.

.

.

.

. and

are subframe logics. To

n

K

KB

K.

T

Alt

give a syntactic characterization of subframe logics we require the following

formulas.

For a formula . and a variable p not occurring in . define a formula .

p

inductively by taking

p

q

⊆ q

p" q an atom"

(:

?)

⊆ :

?

"

for

"

"

"

p

.

p

p

$

p

$

p

$ ? f.

,

.g

.

.

(

:)

⊆

(p

:

)

p

.

.

and put .

⊆ p

.

.

sf

p

.

LEMMA 1.77

⊆ .

.

For any frame

.

i,

is valid in al l subframes of

F

F

sf

F

:

j

Proof

M

F

M

It suffices to notice that if

is a model based on

.

a model

.

based on the subframe of

induced by

y : (

" y)

⊆ p

and (

" x)

⊆ q iff

F

M

M

M

M

M

(

" x)

⊆ q . for all variables q . then (

" x)

⊆ .

iff (

" x)

⊆ .

.

.

.

f

j

g

j

p

j

j

j

PROPOSITION 1.76

The fol lowing conditions are equivalent for any modal

logic

L

"

(i) L

is a subframe logic'

sf

(ii) L ⊆

.

: .

Φ

. for some set of formulas

Φ

'

K

(iii) L

is characterized by a class of frames closed under subframes:

" f

?

g

Proof

The implication (i)

(iii) is trivial4 (iii)

(ii) and (ii)

(i) are

consequences of Lemma 1.77.

.

8

8

8

It follows that the class of subframe logics forms a complete sublattice of

NExt

. However. not all of them have FMP and even are Kripke complete.

K

EXAMPLE 1.78 Let L be the logic of the frame

constructed in Exam-

F

ple 1.8. Since every rooted subframe

of

is isomorphic to a generated

G

F

subframe of

. L is a subframe logic. We show that L has the same Kripke

F

frames as

.

. Suppose

is a rooted Kripke frame for

.

refuting

GL

5

GL

5

G

.

L. Then clearly

contains a finite subframe

refuting . Since

is

G

H

H

?

a finite chain of irreflexive points. it is isomorphic to a generated subframe

of

. contrary to

⊆ . Thus

⊆ L. Conversely. suppose

is a Kripke

F

F

G

G

frame for L. Then

is irreflexive. For otherwise

refutes the formula

G

G

'j

j

. ⊆

(

p

p)

(

p

p)

p. which is valid in

. Let us show

.

.

.

.

.

F

,

now that

is transitive. Suppose otherwise. Then

refutes the formula

G

G

.

.

.

.

.

.

.

.

F

p

(

p

(

q

q)). which is valid in

because ' is a reflexive point.

.

,

.

Finally. since

⊆ .

is Noetherian and since

is of width 1. we may

G

G

F

j

(fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

conclude that

⊆

.

. It follows that the subframe logic L is Kripke

G

GL

5

incomplete. Indeed. it shares the same class of Kripke frames with

.

GL

5

j

but

p

p

.

L.

GL

5

.

.

.

?

[

The following theorem provides a frame-theoretic characterization of those

complete subframe logics in NExt

that are elementary.

!persistent and

K

strongly complete. Say that a logic L has the

if

.nite embedding property

D

a Kripke frame

validates L whenever all finite subframes of

are frames

F

F

for L.

THEOREM 1.76 (Fine 1967)

L

For each Kripke complete subframe logic

the fol lowing conditions are equivalent"

(i) L

is universal'

—

(ii) L

is elementary'

(iii) L

is

9persistent'

D

(iv) L

is strongly Kripke complete'

(v) L

has the .nite embedding property:

Proof

The implications (i)

(ii) and (iii)

(iv) are trivial4 (ii)

(iii)

follows from Fine's [1987b] Theorem formulated in Section 1.2 and (v)

8

8

8

(i) from [Tarski 1975]. Thus it remains to show that (iv)

(v). Suppose

8

F

F

is a Kripke frame with root r such that

⊆ L but all finite subframes

8

of

validate L. Then it is readily checked that all finite subsets of Φ ⊆

F

'j

p

r

 F are L-consistent. Hence the whole set Φ is L-consistent. On

.,

.

f

g 6

the other hand. similarly to the proof of Lemma 1.12 one can show that Φ is

satisfiable in a Kripke frame iff the frame is subreducible to

. So Φ cannot

F

be satisfied in a Kripke frame for L and L is not strongly complete.

.

A similar criterion for the cofinal subframe logics in NExt

can be

K,

found in [Zakharyaschev 1996]. Note. however. that they are not in general

universal and certainly do not have the finite embedding property. but (ii).

(iii) and (iv) are still equivalent.

PROPOSITION 1.79

L

NExt

Every subframe logic

has FMP:

Alt

n

?

Proof

Suppose .

L. By Theorem 1.33. there is a Kripke frame

for L

F

refuting . at a point x. Denote by X the set of points in

accessible from

F

'?

x by

md(.) steps. Clearly. X is finite and the subframe of

induced by

F

7

X validates L and refutes .

.

To understand the place of incomplete logics in the lattice of subframe

logics we call a subframe logic L

if it is Kripke complete

strictly sffficomplete

"

I8e8- universal is the class of Kripke frames for

considered as models of the :rst

L

order language with

and 58

R

ADVANCED MODAL LOGIC

('

o

"

3

o

5

"

"

1

5

"

.

5

.

.

F

G

0

o

o

(a)

(b)

Figure 7.

and no other subframe logic has the same Kripke frames as L. Example 1.78

shows that

.

is not strictly sf-complete. However. the logics

.

and

GL

5

T

S,

Grz

turn out to be strictly sf-complete. The following result clarifies the

situation.

It is proved by applying the splitting technique to lattices of

subframe logics.

THEOREM 1.60

L

A subframe logic

containing

is strictly sffficomplete

K,

i,

L

.

: Al l subframe logics in

are strictly sffficomplete:

NExt

n

GL

5

Alt

'ff

A subframe logic is tabular i, there are only .nitely many subframe logics

containing it:

.,9 More su8cient conditions of FMP

As follows from Theorem 1.73. a logic in NExt

does not have FMP only

K,

if at least one of its canonical axioms contains closed domains. We illustrate

their role by a simple example.

EXAMPLE 1.61 Consider the logic L ⊆

.

—

(

"

) and the formula

K,

5

F

'

—(

"

). where

is the frame depicted in Fig. 7 (a). The frame

in

F

F

G

"

:

:

Fig. 7 (b) separates —(

"

) from L. Indeed.

is a cofinal subframe of

F

F

G

and so

⊆ —(

"

). To show that

⊆ —

(

"

). suppose f is a cofinal

G

F

G

F

:

'

subreduction of

to

. Then f

(1) contains only one point. say x4 f

(0)

5

5

G

F

'j

:

j

:

.

.

also contains only one point. namely the root of

. So the infinite set of

G

points between x and the root is outside domf . which means that f does

not satisfy (CDC) for

1

. On the other hand. if

is a finite refutation

H

frame of width 1 for —(

"

) then

contains a generated subframe reducible

ff

gg

F

H

to

. from which

⊆ L. Thus. L fails to have FMP. In the same manner

F

H

:

the reader can prove that

in Table 3 does not have FMP either.

A

.

'j

We show now two methods developed in [Zakharyaschev 1998a] for es-

tablishing FMP of logics whose canonical axioms contain closed domains.

One of them uses the following lemma. which is an immediate consequence

of the refutability criterion for the canonical formulas.

)[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

LEMMA 1.63

—(

"

)

—(

"

)

—(

"

"

)

—(

"

"

Suppose

and

?

and

)

"

F

D

G

E

F

D

G

E

are canonical formulas such that there is a ?co.nal" subreduction

of

f

G

:

:

to

satisfying ?CDC" for

and an antichain

is in

whenever

domf

F

D

e

E

f (

) ⊆

for some

: Then

?respectively.

—(

"

)

—(

"

)

K,

e

d

d

D

G

E

F

D

ff

3

3

3

?

?

"

—(

"

"

)

—(

"

"

)

":

K,

G

E

F

D

:

?

"

:

THEOREM 1.62 L ⊆

—(

"

"

) : i

I

—(

"

) : j

J

has

i

i

j

j

K,

F

D

F

D

FMP provided that either al l frames

. for

. are irre—exive or al l

i

i

I

J

F

" f

:

?

g " f

?

g

of them are re—exive:

?

6

Proof

F

G

E

Suppose all

are irreflexive and —(

"

"

) is an arbitrary canon-

i

ical formula. We construct from

a new finite frame

by inserting into it

G

H

:

new

points. Namely. suppose

is an antichain in

such that

.

re—exive

e

G

e

E

Suppose also that C

" . . . " C

are all clusters in

such that

C

and

.

n

i

G

e

'?

e

C

⊆

. for i ⊆ 1" . . . " n. but no successor of C

possesses this property.

i

i

ff

3

0

fl

Then we insert in

new reflexive points x

" . . . " x

so that each x

could

.

n

i

G

see only the points in

and their successors and could be seen only from the

e

points in C

and their predecessors. The same we simultaneously do for all

i

antichains

in

of that sort. The resulting frame is denoted by

. Since

e

G

H

no new point was inserted just below an antichain in

.

⊆ —(

"

"

).

E

H

G

E

Suppose now that —(

"

"

)

L and show that

⊆ L. If this is not so

G

E

H

'j

:

then either

⊆ —(

"

"

). for some i

I . or

⊆ —(

"

). for some

i

i

j

j

H

F

D

H

F

D

:

'?

j

j

J . We consider only the former case. since the latter one is treated

'j

:

?

'j

?

similarly. Thus. we have a cofinal subreduction f of

to

satisfying

i

H

F

(CDC) for

. Since

is irreflexive. no point that was added to

is in

i

i

D

F

G

domf . So f may be regarded as a cofinal subreduction of

to

satisfying

i

G

F

(CDC) for

. We clearly may assume also that the subframe of

generated

i

D

G

by domf is rooted. Let

be an antichain in

belonging to domf

and such

e

G

that f (

) ⊆

for some

. If

then there is a reflexive point

i

e

d

d

D

e

E

3

x in

such that x

domf

and x sees only

and. of course. itself. But

H

e

3

3

?

'?

then f (x

) ⊆ f (

) ⊆

and so. by (CDC). x

domf . which is impossible.

e

d

?

3

3

Therefore.

and so. by Lemma 1.63. —(

"

"

)

L. contrary to our

e

E

G

E

3

3

3

?

assumption.

?

:

?

In the case of reflexive frames

points are inserted.

irre—exive

.

EXAMPLE 1.65 According to Theorem 1.62. the logic

1

3

5

5

AK

.—

A

.

L ⊆

—(

"

1

"

1" 3

)

K,

"

5

ff

g

f

gg

has FMP. However. Artemov's logic

⊆ L

does not enjoy this

.

A

GL

property. So FMP is not in general preserved under sums of logics.

"

ADVANCED MODAL LOGIC

)5

The scope of the method of inserting points is not bounded only by canon-

ical axioms associated with homogeneous (irreflexive or reflexive) frames. It

can be applied. for instance. to normal extensions of

with modal reduc-

K,

tion principles. i.e. formulas of the form

p

p. where

and

are

M

N

M

N

strings of

and

(for first order equivalents of modal reduction principles

.

,

.

see [van Benthem 1986]). One can show that each such logic is either of

finite depth. or can be axiomatized by

-formulas and canonical formulas

.,

based upon almost homogeneous frames (containing at most one reflexive

point). for which the method works as well. So we have

THEOREM 1.67

NExt

Al l logics in

axiomatizable by modal reduction

K,

principles have FMP and are decidable:

One of the most interesting open problems in completeness theory of

modal logic is to prove an analogous theorem for logics in NExt

or to

K

construct a counter-example.

It is unknown. in particular. whether the

logics

p

p have FMP4 the same concerns the logics

n

.

K

K

tra

m

n

.

.

"

.

"

The second method of proving FMP uses the more conventional technique

of removing points. Suppose that L ⊆

—(

"

"

) : i

I

and

i

i

K,

G

D

— ⊆ —(

"

"

)

L. Then there exists a frame

for L such that

⊆ —.

H

E

F

F

" f

:

?

g

i.e. there is a cofinal subreduction h of

to

satisfying (CDC) for

.

F

H

E

:

'?

'j

Construct the countermodel

⊆

"

for — as it was done in Section 1.6.

M

F

V

Without loss of generality we may assume that domh

⊆ domh

⊆

and

F

h

i

that

is generated by the sets

(p

). p

a variable in —.

i

i

F

V

3

;

Actually. the step-wise refinement procedure with deleting points having

Sub

—-equivalent successors. used in the proof of Theorem 1.53. establishes

FMP of L when all

are empty. i.e. L is a cofinal subframe logic. To

i

D

tune it for L with non-empty

. we should follow a subtler strategy of

i

D

deleting points. preserving those that are "responsible" for validating the

axioms of L. Suppose we have already constructed a model

⊆

"

M

F

V

.

.

.

n

n

n

h

i

by "folding up" n

1-cyclic sets into clusters of depth n (we use the same

notations as in the proof of Theorem 1.53). Now we throw away points of

[

two sorts.

First. for every proper cluster C of depth n such that some x

C has

a

—-equivalent successor of depth 5 n. we remove from C all points

Sub

?

except x. Second. call a point x of depth " n

in

if it has

redundant

M

.

n

a

—-equivalent successor of depth

n and. for every i

I and every

Sub

cofinal subreduction g of (

)

to the subframe of

generated by some

F

G

.

,

n

i

n

7

?

d

D

d

D

i

i

such that

g(x

) and g satisfies (CDC) for

. there is a point

?

ff

3

y

x

of depth

n such that g(y

) ⊆

. Let X be the maximal

d

?

3

7

3

3

.n

set of redundant points in

which is upward closed in (W

)

. We

.

n

.

n

M

define

⊆

"

as the submodel of

resulting from it by

n

n

n

".

".

".

.

n

M

F

V

M

removing all points in X as well. Since all deleted points have

—-

Sub

h

i

equivalent successors.

⊆ —. And since we keep in

points which

n

".

n

".

M

F

'j

)ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

violate (CDC) for

of possible cofinal subreductions to

.

⊆ L.

i

i

n

".

D

G

F

So FMP of L will be established if we manage to prove that this process

j

eventually terminates.

3

o

"

1

o

o

AK

.—

A

.

EXAMPLE 1.66 Let L ⊆

—(

"

1" 3

"

). where

is

. and

S,

G

G

assume that our "algorithm". when being applied to

. — and L. works

F

"

ff

gg

:

o

infinitely long. Then the frame

⊆

W

" R

. where

,

,

,

F

h

i

i

i

W

⊆

W

" R

⊆

R

"

⊆

W

" R

" P

"

,

,

i

i

i

i

,

,

F

i

i

.

5

.

5

.i.,

.i.,

h

i

is of infinite depth. By K;onig's Lemma. there is an infinite descending

chain . . . x

R

x

. . . R

x

R

x

in

such that x

is of depth i. Since

i

,

i

,

,

,

i

.

,

.

F

5

there are only finitely many pairwise non-

—-equivalent points. there

Sub

must be some n " 0 such that. for every k

n. each point in C (x

) has a

k

Sub

F

F

,

—-equivalent successor in

. And since

is finite. there is m

n

k

.

.k

9

.

starting from which all x

see the same points of depth 1. Let us consider

i

9

now

and ask why points in the m-cyclic set X . folded at step m " 1

m

F

into C (x

). were not removed at step m. X is upward closed in W

m

".

.m

m

and every point in it has a

—-equivalent successor in

. So the only

Sub

,

m

m

F

reason for keeping some x

X is that

is cofinally subreducible to

.

F

G

,

m

,

m

.

x sees inverse images of both points in

but none of its successors in

,

?

.

G

m

F

,

m

does. By the cofinality condition. these inverse images can be taken

.

F

,

from

. But then they are also seen from x

. which is a contradiction.

m

.

Thus sooner or later our algorithm will construct a finite frame separating

L from —. which proves that L has FMP.

The reason why we succeeded in this example is that inverse images of

points in the closed domain

1" 3

can be found at a fixed finite depth in

F

,

. and so points violating (CDC) for it can also be found at finite depth

f

g

(that was not the case in Example 1.61). The following definitions describe

a big family of frames and closed domains of that sort.

A point x in a frame

is called a

of an antichain

in

if x

focus

G

a

G

a

and x

⊆

x

. Suppose

is a finite frame and

a set of antichains

a

G

D

'?

3

f

g 6

3

in

. Define by induction on n notions of

in

(relative to

nffistable point

G

G

D

D

G

) and

in

. A point x is 1-

in

iff either x is of

nffistable antichain

stable

depth 1 in

or the cluster C (x) is proper. A point x is n " 1-

in

stable

G

G

(relative to

) iff it is not m-stable. for any m

n. and either there is an

D

n-stable point in

(relative to

) which is not seen from x or x is a focus

G

D

7

of an antichain in

containing an n

1-stable point and no n-stable point.

D

And we say an antichain

in

is n-stable iff it contains an n-stable point

d

D

[

ADVANCED MODAL LOGIC

)—

1

1

1

1

1

1

1

1

1

o

o

o

o

o

o

o

o

o

"

AK

"(

"

"

AK

.—

"

"

'I

"(

'I

"(

"

"

'I

"(

"

"

'

"

'

"

A

A

.

"

"

'

"

'

'

"

"

'

2

3

3

3

3

3

3

2

2

A

A

.

o

o

o

o

o

o

o

o

o

"

AK

"(

"

"

AK

.—

"

"

'I

"(

'I

"(

"

"

'I

"(

"

"

A

.

A

'

"

'

"

A

A

.

"

A

.

A

"

'

"

'

'

"

"

'

7

5

2

2

2

2

2

7

7

A

A

.

o

o

o

o

o

o

o

o

o

"

AK

"(

"

"

AK

.—

"

"

'I

"(

'I

"(

"

"

'I

"(

"

"

A

.

A

'

"

'

"

A

A

.

"

A

.

A

"

'

"

'

'

"

"

'

8

6

5

5

5

5

5

8

8

A

A

.

o

o

o

o

o

o

o

o

o

6 6 6 6 6 6

6 6 6 6 6 6

6 6 6 6 6 6 6 6 6 6 6

6 6 6 6 6 6

6 6 6 6 6 6

6 6 6 6 6 6

6 6 6 6 6 6 6 6 6 6 6

6 6 6 6 6 6

(a)

(b)

(c)

(d)

Figure 6.

in the subframe

of

generated by

(relative to

) and no m-stable

.

G

G

d

D

point in

(relative to

). for m " n. A point or an antichain is

if

stable

.

G

D

it is n-stable for some n. It should be clear that if a point in an antichain

is stable then the rest points in the antichain are also stable.

EXAMPLE 1.68 (1) Suppose

is a finite rooted generated subframe of one

G

of the frames shown in Fig. 6 (a)!(c). Then. regardless of

. each point

D

in

different from its root is n-stable. where n is the number located near

G

the point. Every antichain

in

. containing at least two points. is also

d

G

n-stable. with n being the maximal degree of stability of points in

.

d

(3) If

is a rooted generated subframe of the frame depicted in Fig. 6

G

(d) and

is the set of all two-point antichains in

then every point in

is

D

G

G

n-stable (relative to

). where n stays near the point. However. for

⊆

D

D

no point in

. save those of depth 1. is stable.

G

fl

(2) If

is a finite tree of clusters then every antichain in

. different from

G

G

a non-final singleton. is either 1- or 3-stable in

regardless of

. Every

G

D

antichain containing a point x with proper C (x) is 1- or 3-stable as well.

whatever

and

are.

G

D

(5) Every antichain is stable in every irreflexive frame

relative to the

G

'

set

of all antichains in

. However. this is not so if

contains reflexive

D

G

G

points (for reflexive singletons are open domains and do not belong to

).

'

D

The sufficient condition of FMP below is proved by arguments that are

similar to those we used in Example 1.66.

THEOREM 1.66

L ⊆

—(

"

"

) : i

I

d " 0

If

and there is

such

i

i

K,

G

D

that. for any

. every closed domain

is

5stable in

?relative

i

I

n

i

i

d

D

G

" f

:

?

g

to

". for some

. then

has FMP:

n

d

L

i

D

?

?

7

Example 1.68 shows many applications of this condition. Moreover. using

it one can prove the following

)(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 1.69

Every normal extension of

with a formula in one vari5

S,

able has FMP and is decidable:

Note that. as was shown by Shehtman [1960]. a formula in two variables

or an infinite set of one-variable formulas can axiomatize logics in NExt

S,

without FMP (and even Kripke incomplete).

.,.0 The reduction method

That a logic does not have FMP (or is Kripke incomplete) is not yet an

evidence of its undecidability:

it is enough to recall that the ma jority of

decidability results for classical theories was proved without using any ana-

logues of the finite model property (see e.g.

[Rabin 1988]. [Ershov 1960]).

The first example of a decidable finitely axiomatizable modal logic without

FMP was constructed by Gabbay [1981].

It seems unlikely that the methods of classical model theory can be ap-

plied directly for proving the decidability of propositional modal logics.

However. sometimes it is possible to

the decision problem for a given

reduce

modal logic L to that for a knowingly decidable first or higher order theory

whose language is expressive enough for describing the structure of frames

characterizing L. The most popular tools used for this purpose are B;uchi's

[1963] Theorem on the decidability of the weak monadic second order theory

of the successor function on natural numbers and Rabin's [1969] Tree The-

orem. Below we illustrate the use of Rabin's Theorem following [Gabbay

1987] and [Cresswell 1965].

Let '

be the set of all finite sequences of natural numbers and

the

.

lexicographic order on it. For x

'

and i 5 ' . put r

(x) ⊆ x

i. where

.

i

%

denotes the usual concatenation operation. Besides. define the following

?

predicates 5

on '

. for 0

i

3.

i

.

7

7

x 5

y iff y ⊆ x

(2n " i) for some n 5 ' .

i

It follows from [Rabin 1969] that the monadic second order theory S'S

of the model

'

"

r

: i 5 '

"

5

: 0

i

3

"

"

(

denotes the empty

.

i

i

sequence) is decidable.

h

f

g

f

7

7

g

%

fli

fl

The theory S'S has a very strong expressive power which makes it pos-

sible to effectively describe semantical definitions of many modal (as well as

some other) logics and thereby prove their decidability. In this way Gabbay

[1987] established the decidability of. for instance.

K

K

p

p"

p

p"

.

,

,

,

.

.

m

m

"

.

"

.

K

K

p

p"

p

p.

.

,

,

.

m

n

m

n

"

.

"

.

ADVANCED MODAL LOGIC

))

By Sahlqvist's Theorem. all these logics are Kripke complete4 however. we

do not know whether they have FMP. General frames can also be described

by means of S'S.

EXAMPLE 1.80 The frame

⊆

W" R" P

constructed in Example 1.8 can

F

be represented in the language of S'S as follows. Let us encode each n 5 '

h

i

by the sequence

2n

. while ' and ' " 1 by r

(

) and r

(

). respectively.

.

,

Then we have

h

i

fl

fl

x

W iff

5

x

x ⊆ r

(

)

x ⊆ r

(

)"

.

.

,

?

fl

,

fl

,

fl

xRy

iff (

5

x

5

y

y

x

x

⊆ y)

.

.

fl

. fl

.

%

.

,

(x ⊆ r

(

)

5

y)

x ⊆ y ⊆ r

(

)

.

.

.

fl

. fl

,

fl

,

(x ⊆ r

(

)

y ⊆ r

(

))"

,

.

fl

.

fl

X

P iff

x (x

X

x

W )

((F in(X )

r

(

) ,

X )

.

?

)

?

.

?

.

.

fl

?

,

Y (

y (y

Y

(y

W

y ,

X ))

F in(Y )

r

(

) ,

Y ))"

.

)

)

?

5

?

.

?

.

.

fl

?

where x ⊆ y means x

y

y

x and

%

.

%

F in(X ) ⊆

x

y (y

X

y

x).

1

)

?

.

%

It follows that the logic Log

is decidable.

Indeed.

for every formula

F

.(p

" . . . " p

). we have .

Log

iff the second order formula

.

n

F

?

x

X

" . . . " X

(X

P

. . .

X

P

x

W

S T (.(X

" . . . " X

)))

.

.

.

n

n

n

)

)

?

.

.

?

.

?

.

belongs to S'S. Here S T (.(X

" . . . " X

)). the

of . is

standard translation

.

n

defined inductively in the following way (see also

):

Correspondence Theory

S T (X ) ⊆ x

X" S T (

) ⊆

"

?

:

:

S T (X

Y ) ⊆ S T (X )

S T (Y )" for

"

"

"

$

$

$ ? f.

,

.g

S T (

X ) ⊆

y (xRy

S T (X )

yfix

).

.

)

.

f

g

Recall that. as was shown in Example 1.78. Log

is Kripke incomplete.

F

Also. it is not hard to find examples of applications of this technique

for proving the decidability of finitely axiomatizable quasi-normal unimodal

and normal polymodal (in particular. tense) logics which do not have Kripke

frames at all4 perhaps. the simplest one is Solovay's logic

.

S

Sobolev [1988a] found another way of proving decidability by applying

methods of automata theory on infinite sequences. Using the results of

[B;uchi and Siefkes 1982] he showed that all finitely axiomatizable superin-

tuitionistic logics of finite width (see Section 2.5) containing the formula

(((p

q)

p)

p)

(((q

p)

q)

q).

.

.

.

,

.

.

.

'
)0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

are decidable. By the preservation theorem of Section 2.2. this result can

be transferred to the corresponding extensions of

.

S,

If a logic is known to be complete with respect to a suitable class of

frames. the methods discussed above are usually applicable to it in a rather

straightforward manner. A relative disadvantage of this approach is that the

resulting decision algorithms inherit the extremely high complexity of the

decision algorithms for S'S or other "rich theories" used to prove decidabil-

ity. On the other hand. the logic

. for instance. turns out to be decidable

S

by an algorithm of the same complexity as that for

(see Example 1.87).

GL

in particular. the derivability problem in

is

-complete. The

S

P SP ACE

logic of the frame

in Example 1.8 is "almost trivial"—it is polynomially

F

equivalent to classical propositional logic. which follows from the fact that

every formula . refutable by

can be also refuted in

under a valua-

F

F

tion giving the same truth-value to all variables in . at all points i such

that

.

5 i 5 ' (see Section 5.6). Actually. this sort of decidability

Sub

j

j

proofs (ignoring "inessential" parts of infinite frames) was used already by

Kuznetsov and Gerchiu [1980] for studying some superintuitionistic logics.

Recently more general semantical methods of obtaining decidability re-

sults without turning to "rich theories" have been developed. We demon-

strate them in the next section by establishing the decidability of all finitely

axiomatizable logics in NExt

.

. which according to Example 1.61 do not

K,

5

in general have FMP. We show. however. that those logics are complete

with respect to recursively enumerable classes of recursive frames in which

the validity of formulas can be effectively checked—it was this rather than

the finiteness of frames that we used in the proof of Harrop's Theorem. In

Section 3.7 this result will be extended to linear tense logics which in general

are not even Kripke complete. Our presentation follows [Zakharyaschev and

Alekseev 1997].

.,. Logics containing

K.

,

.

Each logic in L

NExt

.

is represented in the form

K,

5

?

L ⊆

.

—(

"

"

) : i

I

"

i

i

K,

5

F

D

" f

:

?

g

where all

are chains of clusters. So our decidability problem reduces to

i

F

finding an algorithm which. given such a representation with finite I and

a canonical formula —(

"

"

) built on a chain of clusters

. could decide

F

D

F

whether —(

"

"

)

L. Recall also that. by Fine's [1985c] Theorem. logics

F

D

:

of width 1 are characterized by Kripke frames having the form of Noetherian

:

?

chains of clusters.

ADVANCED MODAL LOGIC

)?

LEMMA 1.81

For any Noetherian chain of clusters

and any canonical

G

formula

—(

"

"

)

.

⊆ —(

"

"

)

i, there is an injective

co.nal subre5

F

D

G

F

D

.

duction

of

to

satisfying ?CDC" for

:

g

G

F

D

:

'j

:

Proof

G

F

D

G

If

⊆ —(

"

"

) then there is a cofinal subreduction f of

to

F

D

satisfying (CDC) for

. Clearly. f

(x) is a singleton if x is irreflexive.

5

'j

:

.

Suppose now that x is a reflexive point in

. Since

contains no infinite

F

G

ascending chains. f

(x) has a finite cover and so there is a reflexive point

5

.

u

f

(x) such that f

(x)

u

. Fix such a u

for each reflexive x and

x

5

5

x

x

.

.

?

ff

;

define a partial map g by taking

f (y)

if either f (y) is irreflexive or

g(y) ⊆

f (y) is reflexive and y ⊆ u

undefined otherwise.

f

y

1

9

1

9

8

One can readily check that g is the injective cofinal subreduction we need.

The converse is trivial.

.

Roughly. every Noetherian chain of clusters refuting —(

"

"

) results

F

D

from

by inserting some Noetherian chains of clusters just below clusters

F

:

C (x) in

such that

x

. We show now that if —(

"

"

) is not in

F

D

F

D

L

NExt

.

then it can be separated from L by a frame constructed

K,

5

f

g '?

:

?

F

from

by inserting in open domains between its adjacent clusters either

finite descending chains of irreflexive points possibly ending with a reflexive

one or infinite descending chains of irreflexive points.

Let C (x

)" . . . " C (x

) be all distinct clusters in

ordered in such a way

.

n

F

that C (x

)

C (x

)

. . .

C (x

)

. Say that an n-tuple t ⊆

[

" . . . " [

.

.

n

.

n

is a

for —(

"

"

) if either [

⊆ m or [

⊆ m". for some m 5 ' . or

type

i

i

F

D

—

; —

—

;

h

i

[

⊆ ' . with [

⊆ 0 if

x

. Given a type t ⊆

[

" . . . " [

for —(

"

"

).

i

i

i

.

n

D

F

D

:

we define the t-

of

to be the frame

that is obtained from

extension

F

G

F

f

g ?

h

i

:

by inserting between each pair C (x

). C (x

) either a descending chain of

i

i

.

5

m irreflexive points. if [

⊆ m 5 ' . or a descending chain of m " 1 points

i

of which only the last (lowest) one is reflexive. if [

⊆ m". or an infinite

i

descending chain of irreflexive points. if [

⊆ ' .

It should be clear that

i

G

F

D

⊆ —(

"

"

).

'j

:

LEMMA 1.83

L

NExt

.

—(

"

"

)

L

—(

"

"

)

If

and

then

is

K,

5

F

D

F

D

separated from

by the

5extension of

. for some type

for

L

t

t

—(

"

"

)

:

F

F

D

?

:

'?

:

:

Proof

By Lemma 1.81. we have a Noetherian chain of clusters

for L

G

and an injective cofinal subreduction f of

to

satisfying (CDC) for

.

G

F

D

By the Generation Theorem. we may assume that f maps the root of

to

G

the root of

. Let

be the subframe of

obtained by removing from

.

F

G

G

G

.1

That is

]

7

5

]

7- for every distinct

dom

8

g

x

g

y

x, y

:

g

.
)fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

all those points that are not in domf but belong to clusters containing some

points in domf . The very same map f is an injective cofinal subreduction

of

to

satisfying (CDC) for

. and so

⊆ —(

"

"

). Since

is a

.

.

.

G

F

D

G

F

D

G

'j

:

reduct of

.

⊆ L.

G

G

.

j

Let C (x

)" . . . " C (x

) be all distinct clusters in

such that

.

.

n

G

n

domf ⊆

C (x

)" C (x

)

C (x

)

. . .

C (x

)

.

i

n

.

.

i

5.

5

—

; —

—

;

By induction on i we define a sequence of frames

. . .

such that

.

n

G

G

(a) f is an injective cofinal subreduction of

to

satisfying (CDC) for

i

G

F

(

(

D

G

. (b) between C (x

) and C (x

) the frame

contains either a finite

i

.

i

i

5

descending chain of irreflexive points possibly ending with a reflexive one

or an infinite descending chain of irreflexive points. and (c)

⊆ L.

G

i

j

Suppose

has been already constructed and

is the chain of clusters

G

C

i

.

5

i

located between C (x

) and C (x

). Three cases are possible. (1)

is a

C

i

.

5

i

i

finite chain of irreflexive points. Then we put

⊆

. (3)

contains

i

i

i

.

G

G

C

5

a non-degenerate cluster C (x) having finitely many distinct successors in

C

i

and all of them are irreflexive. Then

results from

by removing

i

i

.

G

G

5

from

all points save x and those successors.

is a reduct of

i

i

C

G

G

i

.

5

and so conditions (a)!(c) are satisfied.

(2) Suppose (1) and (3) do not

hold. Then

contains an infinite descending chain Y of irreflexive points

i

C

accessible from all other points in

. In this case

is obtained from

i

i

C

G

G

i

.

5

by removing all points in

save those in Y . Clearly.

satisfies (a) and

i

i

C

G

(b). To prove (c) suppose

⊆ —(

"

"

) for some —(

"

"

)

L. Then

i

G

H

E

H

E

there is an injective cofinal subreduction g of

to

satisfying (CDC) for

i

G

H

'j

:

:

?

E

G

H

. Consider g as a cofinal subreduction of

to

and show that it also

i

.

5

satisfies (CDC) for

. Indeed. (CDC) could be violated only by a point in

E

z

Y such that g(z

) ⊆ w

. for some

w

. Since g

(w) is a

i

5

C

E

.

?

[

3

3

f

g ?

singleton and Y

z

. there is y

Y such that g(y

) ⊆ w

and y

domg .

contrary to g satisfying (CDC) for

as a subreduction of

to

.

i

E

G

H

.

ff

3

?

3

3

'?

Thus. a frame separating —(

"

"

)

L from L

NExt

.

can be

F

D

K,

5

found in the recursively enumerable class of t-extensions of

. t being a

F

:

'?

?

type for —(

"

"

). Moreover. given a formula —(

"

"

) and a type t

F

D

H

E

for —(

"

"

). one can effectively check whether —(

"

"

) is valid in the

F

D

H

E

:

:

t-extension of

.

Indeed. let k be the number of irreflexive points in

.

F

H

:

:

t ⊆

[

" . . . " [

. and

the t-extension of

. Construct a cofinal subframe

.

n

G

F

h

i

G

G

F

k

of

by "cutting off" the infinite descending chains inserted in

(if any)

just below their k " 1th points. and let X be the set of all these k " 1th

points. Clearly.

is finite. It is now an easy exercise to prove the following

k

G

LEMMA 1.82

⊆ —(

"

"

)

i, there is an injective co.nal subreduction

G

H

E

f

of

to

satisfying ?CDC" for

and such that

:

X

domf ⊆

k

G

H

E

'j

:

0

fl

ADVANCED MODAL LOGIC

)'

0

5

"

1

5

"

.

.

o o

"(

o

5

.

1

3

'I

"

,

:

'

"

.

.

F

G

0

'

o

5

Figure 8.

As a consequence we obtain

THEOREM 1.85

.

Al l .nitely axiomatizable normal extensions of

are

K,

5

decidable:

.,. Quasiffnormal modal logics

All logics we have considered so far were

. i.e. closed under the rule

normal

of necessitation .,

. McKinsey and Tarski [1956] noticed. however. that

.

by adding to

the McKinsey axiom

⊆

p

p and taking

S,

ma

.,

,.

the closure under modus ponens and substitution we obtain a logic—let us

.

denote it by

.

—which is not normal in that sense. To understand why

S,

:

.

this is so. consider the frame

shown in Fig. 8. One can easily construct

F

a model on

such that 0

⊆

(0 sees a final proper cluster). On the

F

.

ma

other hand.

and all its substitution instances are true at 0 (0 sees a

ma

'j

final simple cluster). from which

.

. : 0

⊆ .

and so

S,

:

.

.

ma

S,

:

.

.

.

A set of modal formulas containing

and closed under modus ponens

K

ff f

j

g

'?

and substitution was called by Segerberg [1981] a

. The

quasiffinormal logic

minimal quasi-normal extension of a logic L with formulas .

. i

I . will be

i

denoted by L "

.

: i

I

(i.e. the operation " presupposes taking the

i

?

closure under modus ponens and substitution only). ExtL is the class of all

f

?

g

quasi-normal logics above L. It is easy to see that a quasi-normal logic is

normal iff it is closed under the congruence rule p

q,

p

q .

.

.

Quasi-normal logics. introduced originally as some abstract (though nat-

5

5

ural) generalization of normal ones. attracted modal logicians' attention

after Solovay [1986] constructed his provability logics

and

. The for-

GL

S

mer one treats

as "it is provable in Peano Arithmetic" and describes

.

those properties of G;odel's provability predicate that are provable in PA4 it

is normal. The latter characterizes the properties of the provability predi-

cate that are true in the standard arithmetic model. and in view of G;odel's

Incompleteness Theorem it cannot be normal. (For a detailed discussion of

provability logic consult

.) Solovay showed

Modal Logic and Selfffireference

0[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

in fact that

S

GL

⊆

"

p

p.

.

.

At first sight

may appear to be inconsistent: L;ob's axiom requires frames

S

to be irreflexive. while

p

p is refuted in them. And indeed. no Kripke

.

frame validates both these axioms (in particular no consistent extension of

.

S

is normal).

Having the algebraic semantics for normal modal logics. it is fairly easy to

construct an adequate algebraic semantics for a consistent L

Ext

. Let

K

M be a normal logic contained in L (for instance the greatest one. which is

?

called the

of L) and

its Tarski!Lindenbaum algebra (in Section

kernel

M

A

11 of

it was called the canonical modal algebra for M ).

Basic Modal Logic

The set

⊆

[.]

: .

L

M

r

f

?

g

is clearly a filter in

. By the well known properties of the Tarski!

M

A

Lindenbaum algebras. we then obtain the following completeness result:

.

L iff under every valuation in

the value of . belongs to

. Struc-

M

A

?

r

tures of the form

"

. where

is a modal algebra and

a filter in

. are

A

A

A

known as

. Thus. every quasi-normal logic is characterized

modal matrices

h

ri

r

by a suitable class of modal matrices. It is not hard to see that L is normal

iff it is characterized by a class of modal matrices with unit filters.

Now. going over to the dual (Stone!Joonsson!Tarski representation)

A

"

of

in a modal matrix

"

and taking

to be the set of ultrafilters in

"

A

A

A

A

containing

. we arrive at the general frame

with the set of

distin5

"

h

ri

r

guished points

actual worlds

(or

)

. A formula . is regarded to be valid

r

"

r

in

"

iff under any valuation in

. . is true at all points in

.

"

"

"

"

A

A

h

r

i

r

Taking into account the Generation Theorem. we can conclude that ev-

ery quasi-normal modal logic is characterized by a suitable class of rooted

general frames in which the root is regarded to be the only actual world.

It follows in particular that. as was first observed by McKinsey and Tarski

[1956].

K,

K,

"

.

: i

I

⊆

.

: i

I

.

i

i

.

.

f

?

g

" f

?

g

However. one cannot replace here

by

or

. Note also that as was

K,

K

T

shown by Segerberg [1981].

.

and some other standard normal logics

K

T

are not finitely axiomatizable with modus ponens and substitution as the

only postulated inference rules. Duality theory between modal matrices and

frames with distinguished points can be developed along with duality theory

for normal logics (for details see [Chagrov and Zakharyaschev 1998]). Kripke

frames with distinguished points were used for studying quasi-normal logics

by Segerberg [1981]. Modal matrices were considered by Blok and K;ohler

[1962] (under the name of filtered algebras). Chagrov [1967b]. and Shum

[1967].

ADVANCED MODAL LOGIC

05

EXAMPLE 1.87 Consider the (transitive) frame

⊆

V " S" Q

whose un-

G

derlying Kripke frame is shown in Fig. 8 and Q consists of

. V . all ,-

h

i

nite sets of natural numbers and the complements to them in the space

fl

V (so '

X

Q iff there is n 5 ' such that m

X for all m

n).

Since

is irreflexive and Noetherian. it validates

. Moreover. we have

G

GL

?

?

?

9

G

.

.

" '

⊆

p

p4 for if under some valuation '

⊆

p then p must be true

h

i j

.

j

at every point. It follows that

with actual world ' validates

. (The

G

S

reader can check that by making ' reflexive we again obtain a frame for

.)

S

By inserting the "tail"

as in Fig. 8 into finite rooted frames for

G

GL

below their roots and using the fact that

has FMP. one can readily

GL

show that. for every formula .

.

iff

(

:

:)

.

.

S

GL

.

?

.

.

?

.

Sub

"

5

.

:

It follows in particular that

is decidable.

S

This example shows that the concepts of Kripke completeness and FMP

do not play so important role in the quasi-normal case: even simple logics

require infinite general frames. One possible way to cope with them at

least in the transitive case is to extend the frame-theoretic language of the

canonical formulas to the class Ext

.

K,

Notice first that the canonical formulas. introduced in Section 1.6. cannot

axiomatize all logics in Ext

. Indeed.

" w

⊆ —(

"

"

) iff there is a

K,

G

F

D

cofinal subreduction f of

to

satisfying (CDC) for

and the following

G

F

D

h

i 'j

:

actual world condition

as well:

(AWC) f (w) is the root of

.

F

Now. consider the frame

" '

constructed in Example 1.87. Since each set

G

X

Q containing ' is infinite and has a dead end. it is impossible to reduce

h

i

?

X to

or

. and so

" '

validates all normal canonical formulas. On the

G

o

5

h

i

other hand. we clearly have

" '

⊆ B

for every n

1. So the logics

n

G

KfiBD

n

cannot be axiomatized by normal canonical formulas without the

h

i 'j

9

postulated necessitation.

To get over this obstacle we have to modify the definition of subreduction

so that such sets as X above may be "reduced" at least to irreflexive roots

of frames. Given a frame

⊆

V " S" Q

with an

root u and a

irre—exive

G

frame

⊆

W" R" P

. we say a partial map f from W onto V is a

quasi5

F

h

i

subreduction

of

to

if it satisfies (R1) for all x" y

domf such that

h

i

F

G

f (x)

⊆ u or f (y)

⊆ u. (R3) and (R2).

Thus. we may map all points in

.

?

the frame

in Fig. 8 to

. and this map will be a quasi-reduction of

to

G

G

satisfying (AWC). Actually. every frame is quasi-reducible to

.

5

5

5

.

Another possibility is to allow 1reductions9 of

to reoexive points by relaxing ]Rff76

X

cf8 Section ff808

'
'
0ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Now. given a finite frame

with an irreflexive root a

and a set

of

.

F

D

antichains in

. we define the

—

(

"

"

)

quasiffinormal canonical formula

0

F

F

D

as the result of deleting

p

from .

in —(

"

"

) (which says that a

is not

.

.

.

.

F

D

:

self-accessible)4 the

quasiffinormal negation free canonical formula

—

(

"

)

0

F

D

:

is defined in exactly the same way. starting from —(

"

). It is not hard

F

D

to see that —

(

"

"

) (or —

(

"

)) is refuted in a frame

" w

iff there

0

0

F

D

F

D

G

is a cofinal (respectively. plain) quasi-subreduction of

to

satisfying

G

F

:

h

i

(CDC) for

and (AWC). The following result is obtained by an obvious

D

generalization of the proof of Theorem 1.55 to frames with distinguished

points (for details see [Zakharyaschev 1993]).

THEOREM 1.86

There is an algorithm which. given a modal ?negation

free" formula

. constructs a .nite set

of normal and quasiffinormal ?nega5

.

tion free" canonical formulas such that

" . ⊆

"

:

K,

K,

For example.

⊆

" —(

) " —(

). Since frames for

are reflexive.

S

K,

S,

we have

o

5

COROLLARY 1.88

There is an algorithm which. given a modal formula

.

. constructs a .nite set

of normal canonical formulas built on re—exive

frames such that

" . ⊆

"

:

S,

S,

As a consequence we obtain

THEOREM 1.86 (Segerberg 1987) Ext

.

⊆ NExt

.

S,

5

S,

5

:

Proof

S,

5

We must show that every logic L

Ext

.

is normal. i.e. .

L

only if

.

L. for every . Suppose otherwise. Then by Corollary 1.88.

.

?

?

there exists —(

"

"

)

L such that

—(

"

"

)

L. Let

" w

be a

F

D

F

D

G

.

?

frame validating L and refuting

—(

"

"

). Since

⊆

.

.

is a chain

.

F

D

G

G

S,

5

:

?

:

'?

h

i

of non-degenerate clusters. And since it refutes —(

"

"

) there is a cofinal

:

j

F

D

subreduction f of

to

. It follows. in particular. that

is also a chain

G

F

F

:

of non-degenerate clusters and so

⊆

. Let a be the root of

. Define a

D

F

map g by taking

fl

f (x)

if x

domf

?

.

g(x) ⊆

a

if x

f

(a)

domf

1

5

undefined otherwise.

?

; [

9

8

It should be clear that g cofinally subreduces

to

and g(w) ⊆ a. Conse-

G

F

quently.

" w

⊆ —(

"

). which is a contradiction.

G

F

.

h

i 'j

:

Let us now briefly consider quasi-normal analogues of subframe and co-

final subframe logics in NExt

. Those logics that can be represented in

K,

the form

K,

F

F

F

(

—(

) : i

I

) "

—(

) : j

J

"

—0 (

) : k

K

i

j

k

" f

?

g

f

?

g

f

?

g

ADVANCED MODAL LOGIC

0—

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

A

.

r

ir

ir

F

F

F

F

u

.

0

1

0

1

".9

,

0

:

5

o

5

5

"

"

1

1

.

.

5

.

5

.

.

.

[

3

'

5

[

"

5

[

1

5

[

Figure 6.

are called (

)

and those of the form

quasiffinormal

subframe logics

K,

F

F

F

(

—(

"

) : i

I

) "

—(

"

) : j

J

"

—0 (

"

) : k

K

i

j

k

" f

:

?

g

f

:

?

g

f

:

?

g

are called (

)

. The classes of quasi-

quasiffinormal

co.nal subframe logics

normal subframe and cofinal subframe logics are denoted by

and

. respectively. The example of

shows that Theorem 1.73 cannot

S

QSF

QC SF

be extended to

and

. Yet one can show that all finitely axiom-

atizable logics in

and

are decidable. We omit almost all proofs

QSF

QCS F

and confine ourselves mainly to formulations of relevant results. For details

QSF

QC SF

the reader is referred to [Zakharyaschev 1996].

We use the following notation. For a frame

⊆

W" R

with irreflexive

F

root u and 0 5 [ 5 ' .

and

denote the frames obtained from

F

F

F

1

1

ir

r

h

i

by replacing u with the descending chains 0" . . . " [

1 of irreflexive and

reflexive points. respectively4

: ⊆

W

" R

: " P

is the

F

:

:

1

".9

,

1

".9

,

1

".9

1

".9

,

,

ir

ir

[

frame that results from

by replacing u with the infinite descending chain

F

D

E

0" 1" . . . of irreflexive points and then adding irreflexive root ' . with P

1

".9

,

:

containing all subsets of W

u

. all finite subsets of natural numbers

0" 1" . . .

. all (finite) unions of these sets and all complements to them in

[ f

g

f

g

the space W

(see Fig. 6). Note that

is a quasi-reduct of every frame

1

".9

,

:

F

of the form

.

or

: .

F

F

F

1

1

1

".9

,

ir

r

ir

The following theorem characterizes the canonical formulas belonging to

logics in

and

.

QS F

QCSF

THEOREM 1.89

L

Suppose

is a subframe or co.nal subframe quasiffinormal

logic: Then

(i)

for every .nite frame

with root

.

i,

'

u

—(

"

"

)

L

" u

⊆ L

F

F

D

F

(ii)

u

—

(

"

"

)

L

for every .nite frame

with irre—exive root

.

i,

0

F

F

D

:

?

h

i 'j

:

?

F

F

F

" u

⊆ L

" 0

⊆ L

.

and

: " '

⊆ L

:

.

1

".9

,

r

ir

h

i 'j

h

i 'j

'j

D

E

Proof

G

F

D

We prove only (

) of (ii). Let

⊆

V " S" Q

refute —

(

"

"

) at

0

its root w and show that

" w

⊆ L. We have a cofinal quasi-subreduction

G

⊆

h

i

:

h

i 'j

0(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

f of

to

such that f (w) ⊆ u. Consider the set U ⊆ f

(u)

Q. Without

5

G

F

.

loss of generality we may assume that U ⊆ U

. There are three possible

?

cases.

;

Case

1. The point w is irreflexive and

w

Q. Then the restriction of

f to domf

(U

w

) is a cofinal subreduction of

to

satisfying (AWC)

f

g ?

G

F

and so

" w

⊆ L.

G

[

[ f

g

h

i 'j

Case

3. There is X

U such that w

X

Q and. for every x

X .

there exists y

X

x

. Then the restriction of f to domf

(U

X ) is a

ff

?

?

?

cofinal subreduction of

to

satisfying (AWC) and so again

" w

⊆ L.

G

F

G

.

?

0

3

r

[

[

Case

2. If neither of the preceding cases holds then. for every X

U

h

i 'j

such that w

X

Q. the set D

⊆ X

X

of dead ends in X is a cover

X

ff

for X . i.e. X

D

. and w

X

D

Q. Put

X

X

?

?

[

;

ff

;

?

[

?

X

⊆ D

" . . . " X

⊆ D

" . . . " X

⊆ U

X

.

U

n

,

1

.

".

U

X

"""

X

1

.

n

9

5

ff

ff

[

1.,

5

Each of these sets. save possibly X

. is an antichain of irreflexive points

,

and belongs to Q. Besides. X

X

⊆

X

for every n 5 6

' .

9

n

1

n.1

,

—

;

,

7

Therefore. the map g defined by

S

g(x) ⊆

?

[

f (x)

if x

V

U

0

[

if x

X

" 0

[

'

1

?

7

7

is a cofinal quasi-subreduction of

to

:

satisfying (AWC).

1

".9

,

G

F

ir

Now using the fact that

: " '

⊆ L and that the composition of

ir

F

1

".9

,

D

E

'j

(cofinal) (quasi-) subreductions is again a (cofinal) (quasi-) subreduction. it

is not hard to see that

" w

⊆ L.

G

.

h

i 'j

COROLLARY 1.60

Al l subframe and co.nal subframe quasiffinormal logics

above

have FMP:

S,

EXAMPLE 1.61 As an illustration let us use Theorem 1.89 to characterize

those normal and quasi-normal canonical formulas that belong to

. Clearly.

S

either —(

) or —(

) is refuted at the root of every rooted Kripke frame. So all

normal canonical formulas are in

. Every quasi-normal formula —

(

"

"

)

0

S

F

D

o

5

associated with

containing a reflexive point is also in

. since

—(

) is

F

S

.

:

refuted at the roots of

.

and

: . But no quasi-normal formula

F

F

F

.

1

".9

,

r

ir

o

—

(

"

"

) built on irreflexive

belongs to

. because

:

⊆ —(

) and

0

F

D

F

F

S

1

".9

,

ir

:

j

o

ir

F

: " '

⊆ —(

). since

'

P

. Notice that incidentally we have

:

1

".9

,

1

".9

,

D

E

j

5

f

g '?

proved the following completeness theorem for

.

S

THEOREM 1.63

is characterized by the class

S

ir

F

F

:

" '

:

1

".9

,

is a .nite rooted irre—exive frame

.

f

g

D

E

ADVANCED MODAL LOGIC

0)

Theorem 1.89 reduces the decision problem for a logic L in

or

to the problem of verifying. given a finite frame

with root u.

F

QS F

QC SF

r

ir

whether

" u

.

" 0

and

: " '

refute an axiom of L. The two

F

F

F

h

i

h

i

D

E

.

1

".9

,

former frames present no difficulties: they are finite. As to the latter. it is

not hard to see that. for instance.

: " '

⊆ —

(

"

) iff

" [

1

.

F

G

F

1

".9

,

0

1

ir

ir

for some [

. is cofinally quasi-subreducible to

. Thus we obtain

G

G

D

E

D

E

'j

:

[

7 j

j

THEOREM 1.62

Al l .nitely axiomatizable subframe and co.nal subframe

quasiffinormal logics are decidable:

One can also give a frame-theoretic characterization of the classes

and

similar to Theorem 1.72. Let us say that a frame

with actual

F

QSF

QCSF

world u is a (

)

of a frame

with actual world w if

is a

co.nal

subframe

G

F

(cofinal) subframe of

and u ⊆ w.

G

THEOREM 1.65 L

L

is a ?co.nal" subframe quasiffinormal logic i,

is char5

acterized by a class of frames with actual worlds that is closed under ?co.nal"

subframes:

.,.: Tabular logics

Every logic L having the finite model property can be represented as the in-

tersection of some

. that is logics characterized by finite frames

tabular logics

(or models. algebras. matrices. etc.):

L ⊆

Log

:

is a finite frame for L

.

F

F

f

g

,

(It follows in particular that every fragment of L containing only those

formulas whose length does not exceed some fixed n 5 ' is determined

by a finite frame4 for that reason logics with FMP are also called

.nitely

approximable

.) In many respects tabular logics are very easy to deal with.

For instance. the key problem of recognizing whether a formula . belongs

to a tabular L is trivially decided by the direct inspection of all possible

valuations of .'s variables in the finite frame characterizing L. That is

why the question "is it tabular?" is one of the first items in the standard

"questionnaire" for every new logical system.

First results concerning the tabularity of modal logics were obtained by

G;odel [1923] and Dugundji [1950] who showed that intuitionistic proposi-

tional logic and all Lewis' modal systems

!

are not tabular. (Note that

S:

S.

using the same method Drabboe [1968] proved that the three non-normal

Lewis' systems

!

cannot be characterized by a matrix with a finite

S:

S5

number of distinguished elements). For arbitrary logics in Ext

one can

K

00

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

easily prove the following syntactical criterion of tabularity. which uses the

formulas

—

⊆

(.

(.

(.

. . .

.

) . . .))"

n

n

.

,

:

,

,

,

-

.

.

.

.

n

.

5

]

⊆

(

.

. . .

.

)"

n

n

.

m

,

,

,

-

.

.

m

.

5.

where .

⊆ p

. . .

p

p

p

. . .

p

.

i

i

i

i

n

.

.

".

.

.

. -

.

.

.

5

tab

n

n

n

⊆ —

]

"

.

THEOREM 1.67 L

Ext

n

L

K

tab

is tabular i,

. for some

n 5 '

:

?

?

Proof

F

A frame

⊆

W" R

refutes —

at a point x

iff a chain of length n

n

.

starts from x

. and

refutes ]

at x

iff there is a chain x

Rx

R . . . Rx

.

.

.

,

n

m

h

i

F

of length m 5 n such that x

is of branching n. i.e. x

Ry

" . . . " x

Ry

m

m

m

n

.

for some distinct y

" . . . " y

. It follows that every rooted generated (by an

.

n

actual world) subframe of the canonical frame for L containing

has at

n

tab

most 1 " (n

1) " . . . " (n

1)

points.

5

n

,

.

[

[

As a consequence we immediately obtain

COROLLARY 1.66

Every tabular modal logic has .nitely many extensions

and al l of them are also tabular:

The next theorem follows from general algebraic results of [Blok and

K;ohler 1962]4 equally easy it can be proved using the characterization above.

THEOREM 1.68

L

Ext

Every tabular logic

is .nitely axiomatizable:

K

?

Proof

K

tab

According to Theorem 1.67. L is an extension of

"

. for some

n

n 5 ' . By Corollary 1.66. we have a chain

K

tab

"

⊆ L

L

. . .

L

L

⊆ L

n

k

k

.

,

.

—

—

—

—

5

of quasi-normal logics such that

L

Ext

: L

L

L

⊆

. for

K

.

i

.

i

".

every i ⊆ 1" . . . " k

1. It remains to notice that if L

is finitely axiomatizable.

.

f

?

—

—

g

fl

L

L

and there is no logic located properly between L

and L

then L

.

.

.

.

.

[

—

is also finitely axiomatizable (e.g. L

⊆ L

" . for any .

L

L

).

.

.

.

.

.

?

[

Theorem 1.13 provides us in fact with an algorithm to decide. given a

tabular logic L

NExt

and an arbitrary formula . whether

. ⊆ L.

K,

K,

Indeed. notice first that we have

?

"

ADVANCED MODAL LOGIC

0?

THEOREM 1.66

L

NExt

Each .nitely axiomatizable logic

of .nite

K,

depth is a .nite unionffisplitting. i:e:. can be represented in the form

?

L ⊆

—

(

"

) : i

I

i

K,

F

'

" f

:

?

g

with .nite

:

I

Proof

K,

Let L ⊆

. be a logic of depth n and let m be the number of

variables in . We show that L coincides with the logic

"

'

m

n

".

L. ⊆

—

(

"

) :

3

c

(i)"

⊆ .

m

K,

G

G

G

" f

:

j

j 7

'j

g

i

5.

X

(c

(i) was defined in Section 1.3). The inclusion L

L

is obvious. Suppose

m

.

.

L

. Then there is a rooted refined m-generated frame

for L

refuting

.

.

(

F

'?

'

. Clearly.

is of depth

n. since otherwise —

(

"

) is an axiom of L

.

F

G

for every rooted generated subframe

of

of depth n " 1 and so

⊆ L

.

.

G

F

F

7

:

which is a contradiction. But then —

(

"

) is an axiom of L

. contrary to

.

F

'

'j

our assumption.

:

.

Thus. all tabular logics in NExt

are finite union-splittings and so. by

K,

Theorem 1.13. we obtain the following

THEOREM 1.69

L

NExt

Let

be a tabular logic in

:

K,

(i) (Blok 1960c) L

has .nitely many immediate predecessors and they are

also tabular:

(ii)

L

The axiomatizability problem for

above

is decidable:

K,

For logics in NExt

this is not the case. witness Theorems 1.26 and 5.12.

K

The tabularity criterion of Theorem 1.67 is not effective. Moreover. as

we shall see in Section 5.5. no effective tabularity criterion exists in general.

However. if we restrict attention to sufficiently strong logics. e.g. to the

class NExt

. the tabularity problem turns out to be decidable. The key

S,

idea. proposed by Kuznetsov [1981]. is to consider the so called pretabular

logics.

A logic L

(N)ExtL

is said to be

in the lattice (N)ExtL

. if

pretabular

.

.

L is not tabular but every proper extension of L in (N)ExtL

is tabular. In

.

?

other words. a pretabular logic in (N)ExtL

is a maximal non-tabular logic

.

in (N)ExtL

.

.

THEOREM 1.90

Ext

NExt

In the lattices

and

every nonffitabular logic

K

K

is contained in a pretabular one:

0fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

1

5

"

3

a

.

.

5

.

.

m

Pi

HY

P

5

"

a

.

HY

'I

'I

H

P

H

5

"

P

5

"

H

H

P

'

H

P

'

H

n

a

b

b

,

.

,

.

?)

5

5

5

5

6 6 6

5

5

5

6 6 6

.—

"(

.—

"(

.

.

?

"

.

"

?

.

"

1

?

a

:

.

"

.

"

5

"

?

.

"

?

5

"

.

"

a

'

5

"

5

"

.

5

.

.

,

,

,

5

5

G

G

G

m:n

,

,

:

Figure 9.

Proof

By Theorem 1.67. a logic is non-tabular iff it does not contain the

formula

. for any n 5 ' .

It follows that the union of an ascending

n

tab

chain of non-tabular logics is a non-tabular logic as well. The standard use

of Zorn's Lemma completes the proof.

.

If there is a simple description of all pretabular logics in a lattice. we

obtain an effective (modulo the description) tabularity criterion for the lat-

tice. Indeed. take for definiteness the lattice NExt

. How to determine.

K,

given a formula . whether

. is tabular? We may launch two parallel

K,

processes: one of them generates all derivations in

. and stops after

K,

"

finding a derivation of

. for some n 5 ' 4 another process checks if .

n

tab

"

belongs to a pretabular logic in NExt

and stops if this is the case. The

K,

termination of the first process means that

. is tabular. while that of

K,

the second one shows that it is not tabular.

"

Unfortunately. it is impossible to describe in an effective way all pretab-

ular logics in (N)Ext

and even (N)Ext

: Blok [1960c] and Chagrov

K

K,

[1969] constructed a continuum of them. However. for smaller lattices like

NExt

or NExt

such descriptions were found by Maksimova [1987b].

S,

GL

Esakia and Meskhi [1988] and Blok [1960c]. The five pretabular logics in

NExt

were presented in Section 18 of

. In NExt

Basic Modal Logic

S,

GL

the picture is much more complicated.

THEOREM 1.91 (Blok 1960c. Chagrov 1969)

The set of pretabular logics

in

NExt

GL

is denumerable: It consists of the logics

and

.

⊆ Log

GL

5

G

,

,

,

,

Log

m

0

n

1

. for

.

. where

and

are the frames depicted in

G

G

G

m:n

m:n

Fig: (: If

m" n

⊆

k " l

then

Log

⊆ Log

:

G

G

m:n

k:l

9

9

,

,

h

i '

h

i

Using this semantic description of pretabular logics in NExt

. it is not

GL

'
ADVANCED MODAL LOGIC

0'

hard to find finite sets of formulas axiomatizing them. Moreover. all of them

turn out to be decidable. For we have

THEOREM 1.93

L

NExt

Every nonffitabular logic

has a nonffitabular

K,

extension with FMP. and so every pretabular logic in

has FMP:

NExt

K,

?

Proof

Since L is non-tabular and characterized by the class of its rooted

finitely generated refined frames. we have either a sequence

. i ⊆ 1" 3" . . .

i

F

of rooted finite frames for L of depth i. or a sequence

of rooted finite

F

i

F

frames for L of width

i. In both cases the logic Log

: i 5 '

L is

i

non-tabular and has FMP.

.

9

f

g (

So we obtain the following result on the decidability of tabularity.

THEOREM 1.92

NExt

Ext

The property of tabularity is decidable in

.

.

S,

S,

NExt

Ext

.

:

GL

GL

Since a logic in Ext

is locally tabular iff it is determined by a frame

K,

of finite depth. the property of local tabularity is decidable in the lattices

mentioned in Theorem 1.92 as well. However. this is not the case for Ext

K,

itself.

.,." Interpolation

One of the fundamental properties of logics is their capability to provide

explicit definitions of implicitly definable terms. which is known as the Beth

property (Beth [1972] proved it for classical logic). In the modal case we

say a logic L has the

if. for any formula .(p

" . . . " p

" p

)

Beth property

.

".

n

n

and variables p and q different from p

" . . . " p

.

.

n

.(p

" . . . " p

" p)

.(p

" . . . p

" q)

(p

q)

L

.

.

n

n

.

.

5

?

only if there is a formula :(p

" . . . p

) such that

.

n

.(p

" . . . " p

" p)

(p

:(p

" . . . p

))

L.

.

.

n

n

.

5

?

The Beth property turns out to be closely related to the interpolation prop-

erty which was introduced by Craig [1978] for classical logic. Namely. we

say that a logic L has the

if. for every implication

interpolation property

—

]

L. there exists a formula ( . called an

interpolant

for —

] in L.

.

?

.

such that —

(

L. (

]

L and every variable in ( . if any. occurs in

both — and ] . While in abstract model theory interpolation is weaker than

.

?

.

?

Beth definability. for modal logics we have

THEOREM 1.95 (Maksimova 1993)

A normal modal

logic has interpola5

tion i, it has the Beth property:

?[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Say also that a normal modal logic L has the

interpolation property for

the consequence relation

interpolation

.

-

for short. if every time when

.

.

L

"

"

—

] . there is a formula ( such that —

( . (

] and

(

Var

.

L

.

.

L

L

"

"

"

ff

Var

Var

Var

—

] . (Here

. is the set of all variables in ..) It should be

0

clear that interpolation implies

-interpolation.

.

"

By the end of the 1980s interpolation had been established for a good

many standard modal systems. The semantical proofs. sometimes rather

sophisticated. resemble the Henkin construction of the canonical models.

Here are two examples of such proofs (which are due to Maksimova [1963b]

and Smoryonski [1986]).

THEOREM 1.97 (Gabbay 1983)

The logics

.

.

.

have the inter5

K

K,

T

S,

polation property:

Proof

S,

We consider only

4 for the other logics the proofs are similar.

Suppose —

(

and (

]

for any ( whose variables occur in

S,

S,

both — and ] . and show that in this case —

]

.

S,

.

'?

.

'?

Let t ⊆ (Φ"  ) be a pair of sets of formulas such that

.

— if

Var

Var

.

'?

.

Φ and

.

] if .

 . Say that t is

if there are

inseparable

Var

Var

ff

?

ff

?

no formulas .

Φ. :

  and ( with

(

—

] such that

i

j

Var

Var

Var

n

m

?

?

ff

0

i

5.

i

5.

.

(

. (

i

:

i

. The pair t is called

if for

complete

S,

S,

every . and : with

.

— and

:

] . one of the formulas

Var

Var

Var

Var

V

W

.

?

.

?

. and

. is in Φ and one of : and

: is in  .

ff

ff

-

-

LEMMA 1.96

t

⊆ (Φ

"

)

Every inseparable pair

can be extended to a

.

.

.

complete inseparable pair:

Proof

Let .

" .

" . . . and :

" :

" . . . be enumerations of all formulas whose

.

,

.

,

variables occur in — and ] . respectively. Define pairs t

⊆ (Φ

"

) and

.

.

.

n

n

n

t

⊆ (Φ

"

) inductively by taking

n

n

n

".

".

".

(Φ

.

"

)

if this pair is inseparable

n

n

n

t

.

⊆

n

6 f

g

0

(Φ

.

"

) otherwise.

n

n

n

6 f-

g

(Φ

"

:

)

if this pair is inseparable

.

.

n

n

n

t

⊆

n

".

6 f

g

0

n

n

(Φ

"

:

) otherwise

.

.

n

6 f-

g

and put t

⊆ (Φ

"

). where Φ

⊆

Φ

.

⊆

. Clearly

.

.

.

.

n

.

n

n.,

n.,

t

is complete. Suppose it is separable. i.e. for some .

" . . . " .

Φ

.

.

.

n

.

S

S

:

" . . . " :

and some ( containing only those variables that occur in

.

m

.

?

both — and ] . we have

.

(

and (

i

5.

i

i

5.

:

i

. Then

S,

S,

?

n

m

.

?

.

?

there is k 5 ' such that .

" . . . " .

Φ

and :

" . . . " :

. which means

V

.

.

W

n

k

m

k

that t

is separable. So it remains to show that if t ⊆ (Φ"  ) is inseparable.

k

?

?

Var

Var

Var

Var

.

— and

:

] then

ff

ff

ADVANCED MODAL LOGIC

?5

one of the pairs (Φ

.

"  ) or (Φ

.

"  ) is inseparable and

5

6 f

g

6 f-

g

one of the pairs (Φ"

:

) or (Φ"

:

) is inseparable.

5

6 f

g

6 f-

g

We prove only the former claim. Suppose. on the contrary. that both pairs

are separable. i.e. there are formulas (

. (

in variables occurring in both

.

,

— and ] such that. for some .

" . . . " .

Φ. :

" . . . " :

 . we have

.

.

n

m

?

?

.

. . .

.

.

(

" (

:

. . .

:

"

.

.

.

.

n

m

S,

S,

.

.

.

.

?

.

,

,

?

.

. . .

.

.

(

" (

:

. . .

:

.

.

,

,

.

n

m

S,

S,

.

.

. -

.

?

.

,

,

?

Then we obtain (.

. . .

.

.)

(.

. . .

.

.)

(

(

.

.

.

.

,

n

n

S,

.

.

.

,

.

.

. -

.

,

?

(

(

:

. . .

:

. from which

.

,

.

m

S,

,

.

,

,

?

.

. . .

.

(

(

" (

(

:

. . .

:

"

.

.

,

.

,

.

n

m

S,

S,

.

.

.

,

?

,

.

,

,

?

contrary to t being inseparable.

.

Now we define a frame

⊆

W" R

by taking W to be the set of all

F

complete and inseparable pairs and. for t

⊆ (Φ

"

). t

⊆ (Φ

"

) in W .

.

.

.

,

,

,

h

i

t

Rt

iff

.

Φ

implies .

Φ

. Using the axioms

p

p and

p

p

.

,

.

,

.

.

.

.

of

. one can readily check that R is a quasi-order on W . i.e.

⊆

.

S,

F

S,

?

?

.

.

Define a valuation

in

by taking for every variable p

(—

] ).

V

F

j

Var

V

Var

(p) ⊆

(Φ"  )

W : either p

Φ or p

] and p

. Put

?

.

M

F

V

⊆

"

. By induction on the construction of formulas . and : with

f

?

?

?

'?

g

h

i

Var

Var

Var

Var

.

—.

:

] one can show that for every t ⊆ (Φ"  ) in

F

ff

ff

M

M

(

" t)

⊆ . iff .

Φ" (

" t)

⊆ : iff :

 .

j

?

'j

?

Indeed. the basis of induction follows from the definition of

and the

V

completeness and inseparability of t. The cases of the Boolean connectives

present no difficulty. So suppose . ⊆

.

.

If t

⊆

.

then. for every

.

.

.

.

t

⊆ (Φ

"

)

t

. we have t

⊆ .

and so .

Φ

. Suppose

.

Φ. Then

.

.

.

.

.

.

.

.

j

.

.

.

Φ. Consider the pair t

⊆ (Φ

"

). where

.

.

.

.

?

3

j

?

'?

-

?

Φ

⊆

.

? :

?

Φ

"

⊆

? :

?

"

.

.

.

.

.

f-

g 6 f

?

g

f-

-

?

g

and show that it is inseparable. Assume otherwise. Then there is ( with

Var

Var

Var

(

—

] such that. for some formulas

?

" . . . "

?

Φ.

.

n

.

.

ff

0

?

.

.

?

" . . . "

?

 .

n

".

m

-

-

?

.

?

. . .

?

(

" (

?

. . .

?

.

.

.

n

n

".

m

S,

S,

-

.

.

.

.

?

. -

,

, -

?

It follows that

.

.

.

,

.

?

. . .

?

(

"

.

.

n

S,

-

.

.

.

.

?

?ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

,

.

.

(

?

. . .

?

"

n

".

m

S,

. -

,

, -

?

contrary to t being inseparable. Let t

⊆ (Φ

"

) be a complete inseparable

.

.

.

extension of t

. By the definition of t

. we have tRt

and so .

Φ

. contrary

.

.

.

.

.

to

.

Φ

Φ

and t

being inseparable.

.

.

.

.

?

-

?

ff

.

Suppose now that

.

Φ. Then for every t

⊆ (Φ

"

) such that tRt

.

.

.

.

.

.

we have .

Φ and so t

⊆ .

. Consequently. t

⊆

.

. The formula : is

.

.

.

.

?

.

treated in the dual way.

?

j

j

To complete the proof it remains to observe that

⊆ —

] .

M

.

'j

.

This proof does not always go through for different kinds of logics. How-

ever. sometimes suitable modifications are possible.

THEOREM 1.98

has the interpolation property:

GL

Proof

GL

Suppose —

] has no interpolant in

. Our goal is to construct

a finite irreflexive transitive frame refuting —

] .

.

This time we consider finite pairs t ⊆ (Φ"  ) such that all formulas in Φ

.

and   are constructed from variables and their negations using

.

.

.

.

.

,

Without loss of generality we will assume — and ] to be formulas of that

.

,

sort. Say that t is

if there is a formula ( with

(

—

]

separable

Var

Var

Var

such that

Φ

(

and (

. It should be clear that if

GL

GL

ff

0

t ⊆ (Φ"  ) is a finite inseparable pair then in the same way as in the proof

V

W

.

?

.

?

of Theorem 1.97 but taking only subformulas of — and ] we can obtain

a finite inseparable pair t

⊆ (Φ

"

) satisfying the conditions: for every

8

8

8

.

— and :

] . one of the formulas . and

. (an equivalent

Sub

Sub

?

?

-

8

formula of the form under consideration. to be more precise) is in Φ

and

one of : and

: is in

.

8

-

Now we construct by induction a finite rooted model for

refuting

GL

—

] . As its root we take (

—

"

]

). If we have already put in our

8

8

.

f

g

f

g

model a pair t ⊆ (Φ"  ) and it has not been considered yet. then for every

,

.

.

Φ and every

:

 . we add to the model the pairs

?

?

t

⊆ (

?"

?"

." . :

?

Φ

"

?"

? :

?

)"

.

.

.

.

,

,

8

8

f

-

?

g

f

?

g

t

⊆

?"

? :

?

Φ

"

?"

?"

: " : :

?

).

,

.

.

,

,

,

8

8

f

?

g

f

-

?

g

One can readily show that if t is inseparable then t

and t

are also in-

.

,

separable. Put tR

t

and tR

t

. The process of adding new pairs must

.

.

.

,

eventually terminate. since each step reduces the number of formulas of the

form

. and

: in the left and right parts of pairs. Let W be the set of

,

.

all pairs constructed in this way and R the transitive closure of R

. Clearly.

.

the resulting frame

⊆

W" R

validates

. Define a valuation

in

by

F

V

F

GL

taking. for each variable p.

h

i

V

(p) ⊆

(Φ"  )

W : p

Φ

.

f

?

?

g

ADVANCED MODAL LOGIC

?—

As in the proof of Theorem 1.97. it is easily shown that —

] is refuted in

F

V

under

.

.

.

To clarify the algebraic meaning of interpolation we require the following

well known proposition.

PROPOSITION 1.96

If

is a normal .lter

in a modal algebra

then

A

.,

the relation

. de.ned by

i,

. is a congruence relation:

a

b

a

b

r

The map

is an isomorphism from the lattice of normal .lters in

A

r

r

2

2

5

? r

onto the lattice of congruences in

:

A

r ". 2

r

Denote by

,

the quotient algebra

,

and let

a

⊆

b : a

b

.

A

A

Say that a class

of algebras is

if for all algebras

.

.

amalgamable

.

.

A

A

r

2

k

k

f

2

g

r

r

r

A

A

A

A

,

.

.

,

.

,

in

such that

is embedded in

and

by isomorphisms f

and f

.

C

C

respectively. there exist

and isomorphisms g

and g

of

and

.

,

.

,

A

A

A

into

with g

(f

(x)) ⊆ g

(f

(x)). for any x in

. If in addition we have

.

.

,

,

.

A

A

? C

g

(x)

g

(y) implies

z

A

(x

f

(z ) and f

(z )

y)

i

j

i

i

j

j

.

7

1

?

7

7

for all x

A

. y

A

such that

i" j

⊆

1" 3

. then

is called

superamal5

i

j

gamable

. Here A

is the universe of

and

its lattice order.

i

i

i

A

?

?

f

g

f

g

C

7

THEOREM 1.99 (Maksimova 1989) L

has the interpolation property i, the

variety

of modal algebras for

is superamalgamable:

has the

5

AlgL

L

L

.

"

interpolation property i,

is amalgamable:

AlgL

Proof

We prove only the former claim. (

) Suppose L has the interpo-

lation property and

.

.

are modal algebras for L such that

is

.

.

,

.

A

A

A

A

8

a subalgebra of both

and

. With each element a

A

. i ⊆ 0" 1" 3.

.

,

i

A

A

we associate a variable p

in such a way that. for a

A

. p

⊆ p

⊆ p

.

a

a

a

a

.

i

?

.

.

,

Denote by

the language with the variables p

. for a

A

. i ⊆ 0" 1" 3. and

i

i

a

i

?

let

⊆

. We will assume that

is the language of L.

.

,

L

?

L

L

6 L

L

i

Fix the valuation

of

in

. defined by

(p

) ⊆ a. and put

i

i

i

i

V

A

V

a

L

#

⊆

.

:

(.) ⊆

.

i

i

i

For

V

f

?

L

]g

Let # be the closure of #

#

L under modus ponens. We show that.

.

,

for every .

. :

such that

i" j

⊆

1" 3

.

i

j

For

For

6

6

?

L

?

L

f

g

f

g

.

:

# iff

?

(.

?

#

and ?

:

#

).

(12)

For

.

i

j

.

?

1

?

L

.

?

.

?

Suppose .

:

#. Then there exist finite sets Φ

#

and Φ

#

such

i

i

j

j

.

?

ff

ff

that

.,

Φ

.

(

Φ

:)

L.

i

j

.

.

.

?

.

.

A :lter

is normal ]or open- as in Section 5[ of Basic Modal Logic7 if

r

a

: r

.

whenever

8

a

: r

?(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Since L has interpolation. there is a formula ?

such that

For

.

?

L

Φ

.

?

L"

Φ

(?

:)

L"

i

j

.

.

?

.

.

?

.

.

from which .

?

#

and ?

:

#

. The converse implication is

i

j

obvious.

.

?

.

?

Now construct an algebra

by taking the set

.

: .

#

as its

A

universe. where

.

⊆

: : .

:

#

.

.

:

⊆

.

:

and

fk

k

?

g

.

⊆

.

. for

"

. One can readily prove that

AlgL.

.

A

k

k

f

5

?

g

k

k . k

k

k

.

k

$k

k

k $

k

$ ? f-

g

i

?

Define maps g

from

into

by taking g

(a) ⊆

p

. It is not difficult to

i

i

i

A

A

a

k

k

show that g

is an embedding of

in

. And for a

A

. we have

i

i

.

A

A

g

(a) ⊆

p

⊆ g

(a).

.

,

a

.

k

k

?

It remains to check the condition for superamalgamability: Suppose a

A

.

i

b

A

.

i" j

⊆

1" 3

. and g

(a)

g

(b). Then g

(a)

g

(b) ⊆

and

j

i

j

i

j

?

?

f

g

f

g

j

j

7

.

]

i

i

so

p

p

⊆

. i.e. p

p

#. By (12). we have ?

with

For

.

a

a

b

b

k

.

k

]

.

?

?

L

V

(?) ⊆ c such that a

c

b.

i

j

7

7

(

) Assuming AlgL to be superamalgamable. we show that L has the

⊆

interpolation property. To this end we require

LEMMA 1.100

Suppose

is a subalgebra of modal algebras

and

.

.

.

,

A

A

A

a

A

b

A

c

A

a

c

b

.

and there is no

such that

: Then

.

,

.

.

,

?

?

?

7

7

there are ultra.lters

in

and

in

such that

a

.

b

and

.

.

,

,

.

,

A

A

r

r

? r

'? r

.

.

,

.

A

⊆

A

:

r

0

r

0

Suppose .(p

" . . . " p

" q

" . . . " q

) and :(q

" . . . " q

" r

" . . . " r

) are formu-

.

.

.

.

m

n

n

l

las for which there is no ?(q

" . . . " q

) such that .

?

L and ?

:

L.

.

n

We show that in this case there exists an algebra

VarL refuting .

: .

A

.

?

.

?

Let

.

and

be the free algebras in AlgL generated by the sets

A

A

A

.

.

.

.

.

,

?

.

c

" . . . " c

.

a

" . . . " a

" c

" . . . " c

and

c

" . . . " c

" b

" . . . " b

. respectively.

.

.

.

.

.

n

m

n

n

l

f

g

f

g

f

g

According to this definition.

is a subalgebra of both

and

. By

A

A

A

.

.

.

.

.

,

Lemma 1.100. there are ultrafilters

in

and

in

such that we

A

A

.

.

.

,

.

,

have .(a

" . . . " a

" c

" . . . " c

)

and :(c

" . . . " c

" b

" . . . " b

)

. De-

.

.

.

.

.

,

m

n

n

l

r

r

fine normal filters

? r

'? r

.

⊆

a

A

.

:

m 5 '

a

i

i

i

m

.

r

f

?

)

? r

g

and put

⊆

,

.

⊆

,

. Construct an algebra

by taking

.

,

.

.

.

.

.

A

A

A

A

A

.

.

,

,

A

⊆

a

: a

A

. By the definition.

is a subalgebra of

. i.e. is

.

.

.

.

.

A

A

:

r

r

fk

k

?

g

.

r

embedded in

by the map f

(x) ⊆ x. One can show that

is embedded

.

.

.

A

A

in

by the map f

(

x

) ⊆

x

. Then there are an algebra

for L

A

A

,

,

.

:

k

k

k

k

r

r

:

and isomorphisms g

and g

of

and

into

satisfying the conditions

.

,

.

,

A

A

A

of superamalgamability. Define a valuation

in

by taking

(p

) ⊆

i

V

A

V

ADVANCED MODAL LOGIC

?)

"

'

HY

"

o

H

"

HY

H

H

o

H

H

"

'

"

H

"
H

o

"

'

"8

H

1

HY

"

1

o

'I

o

H

o

1

1

'

H

"

1fl

5

?

H

o

'I

1

o

H

"8

"

'

'

1

'

1

o

1

'

5

?

1fl

o

1

1

'

'

o

1

1

1fl

5

?

o

5

?

Figure 10.

g

(

a

).

(q

) ⊆ g

(

c

) ⊆ g

(

c

) and

(r

) ⊆ g

(

b

).

.

.

,

,

i

j

j

j

k

k

.

.

:

:

V

V

k

k

k

k

k

k

k

k

r

r

r

r

Then

(.)

(:) because otherwise there would exist

i" j

⊆

1" 3

and

V

V

z

A

such that

(.)

f

(z ) and f

(z )

(:). Thus.

⊆ .

: and

.

i

i

j

j

V

V

A

'7

f

g

f

g

?

7

7

'j

.

.

so .

:

L.

.

'?

Using this theorem Maksimova [1989] discovered a surprising fact: there

are only finitely many logics in NExt

with the interpolation property

S,

(not more than 26. to be more exact) and all of them turned out to be

union-splittings. By Theorem 1.13. we obtain then

THEOREM 1.101 (Maksimova 1989)

There is an algorithm which. given a

modal formula

. decides whether

has interpolation:

.

.

S,

"

We illustrate this result by considering a much simpler class of logics.

THEOREM 1.103

NExt

Only four logics in

have the interpolation prop5

S.

erty"

itself. the logic of the twoffipoint cluster.

and

:

S.

Triv

For

Proof

We have already demonstrated how to prove that a logic has inter-

polation. So now we show only that no logic L in NExt

different from

S.

those mentioned in the formulation has the interpolation property. Suppose

on the contrary that L has interpolation. We use the amalgamability of the

variety of modal algebras for L to show that an arbitrary big finite cluster

is a frame for L. from which it will follow that L ⊆

.

S.

?0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Figure 10 demonstrates two ways of reducing the three-point cluster to

the two-point one. By the amalgamation property. there must exist a clus-

ter reducible to the two depicted copies of the two-point cluster. with the

reductions satisfying the amalgamation condition. It should be clear from

Fig. 10 that such a cluster contains at least four points. By the same scheme

one can prove now that every n-point cluster validates L.

.

It would be naive to expect that such a simple picture can be extended

to classes like NExt

or NExt

. Even in NExt

the situation is quite

K,

K

GL

different from that in NExt

: Maksimova [1969] discovered that there is

S,

a continuum of logics in NExt

having the interpolation property. This

GL

result is based upon the following observation. For L

NExt

. we call a

K,

formula —(p)

in NExtL if

conservative

?

"

.

.

(—(

)

—(p)

—(q))

—(p

q)

—(

p)

L.

:

.

.

.

.

.

?

For example. in NExt

conservative are

p

p.

p

p. and

S,

.,

,.

.,

,.

.

5

.

,

p

p.

5

THEOREM 1.102 (Maksimova 1968)

L

NExt

If

has the interpolation

K,

property and formulas

. for

. are conservative in

. then the

—

i

I

NExtL

i

?

logic

also has the interpolation property:

L

—

: i

I

i

?

" f

?

g

Proof

Suppose .

:

L

—

: i

I

. Then there is a finite J

I . say

i

J ⊆

1" . . . " l

. such that .

:

L

—

: i

J

and so. as follows from

i

.

?

" f

?

g

ff

f

g

.

?

" f

?

g

the definition of conservative formulas and the Deduction Theorem for

.

K,

l

"

.

j

.

5.

(—

(

)

—

(p

)

. . .

—

(p

))

(.

:)

L"

j

j

j

n

.

:

.

.

.

.

.

?

where p

" . . . " p

" p

" . . . " p

and p

" . . . " p

" p

" . . . " p

are all the

.

".

".

".

m

m

k

m

k

k

n

variables in . and : . respectively. Consequently

l

"

.

(—

(

)

—

(p

)

. . .

—

(p

))

.

j

j

j

k

.

:

.

.

.

.

.

j

5.

.

l

"

.

(

(—

(p

)

. . .

—

(p

))

:)

L.

j

m

j

n

".

j

.

5.

.

.

.

?

Since L has the interpolation property. there is ?(p

" . . . " p

) such that

m

k

".

l

"

.

j

.

5.

(—

(

)

—

(p

)

. . .

—

(p

))

.

?

L"

j

j

j

k

.

:

.

.

.

.

.

?

ADVANCED MODAL LOGIC

??

l

"

.

j

.

5.

(—

(p

)

. . .

—

(p

))

(?

:)

L.

j

m

j

n

".

.

.

.

.

?

Then we obtain .

?

L

—

: i

I

and ?

:

L

—

: i

I

.

i

i

i.e. ? is an interpolant for .

: in L

—

: i

I

.

i

.

.

?

" f

?

g

.

?

" f

?

g

.

" f

?

g

Using the formulas

—

⊆

(

p

p)

i

.

,

.

.

.

"

".

",

".

".

i

i

i

i

] .

: .

,

-

which are conservative in NExt

. one can readily construct a continuum

GL

of logics in this class with the interpolation property. The set of logics in

NExt

without interpolation is also continual.

GL

In general. an interpolant ( for an implication —

]

L depends on

both — and ] . Say that a logic L has

if. for any

uniform interpolation

.

?

finite set of variables $ and any formula —. there exists a formula ( such

that

(

$ and —

(

L. (

]

L whenever

—

]

$

Var

Var

Var

and —

]

L.

In this case ( is called a

for — and

postffiinterpolant

ff

.

?

.

?

0

ff

$. Roughly speaking. a logic has uniform interpolation if we can choose

.

?

an interpolant for —

]

L independly from the actual shape of ] .

Uniform interpolation was first investigated by Pitts [1993] who proved that

.

?

intuitionistic logic enjoys it.

It is fairly easy to find multiple examples

of modal logics with uniform interpolation by observing that any locally

tabular logic with interpolation has uniform interpolation as well. Indeed.

for every formula — and every set of variables $. we can define a post-

interpolant ( as the conjunction of a maximal set of pairwise non-equivalent

in L formulas (

such that

(

$ and —

(

L (which is finite in view

.

.

.

Var

of the local tabularity of L). It follows. for instance. that

has uniform

S.

ff

.

?

interpolation.

In general. however. interpolation does not imply uniform

interpolation:

[Ghilardi and Zawadowski 1997] showed that

does not

S,

enjoy the latter. witness the following formula without a post-interpolant

for

r

in

S,

f

g

p

(p

q)

(q

p)

(p

r)

(q

r).

.

,

.

,

.

.

.

.

.

.

.

.

.

. -

Only a few positive results on the uniform interpolation of modal logics

are known: Shavrukov [1992] proved it for

. Ghilardi [1997] for

. and

GL

K

Visser [1996] for

.

Grz

A property closely related to interpolation is so called Halldoen com-

pleteness. A logic L is said to be

if .

:

L and

Hal ld)en complete

Var

Var

.

: ⊆

imply .

L or :

L. Since every variable free for-

,

?

0

fl

?

?

mula is equivalent in

either to

or to

. L

Ext

is Halldoen complete

D

D

whenever it has interpolation.

.

.

are examples of Halldoen incom-

K

K,

GL

]

:

?

plete logics with interpolation: each of them contains

but not

,

,

] , -

]

?fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

,

,

and

. On the other hand.

.

is a Halldoen complete logic (see

S,

5

]

-

]

[van Benthem and Humberstone 1962]) without interpolation (see [Maksi-

mova 1963a]). Actually. there is a continuum of Halldoen complete logics in

NExt

(see [Chagrov and Zakharyaschev 1992]).

S,

Halldoen completeness has an interesting lattice-theoretic characteriza-

tion.

THEOREM 1.105 (Lemmon 1966c)

L

Ext

A logic

is Hal ld)en complete

K

i, it is

5irreducible in

ExtL

:

?

T

Since the lattice Ext

is linearly ordered by inclusion. all logics above

S.

S.

are Halldoen complete. There are various semantic criteria for Halldoen

completeness (see e.g. [Maksimova 1997]). Here we note only the following

generalization of the result of [van Benthem and Humberstone 1962].

THEOREM 1.107

L

Ext

Suppose a logic

is characterized by a class

K

of descriptive rooted frames with distinguished roots: Then

is Hal ld)en

L

?

C

complete i,. for al l frames

and

in

. there is a frame

" d

" d

" d

.

.

,

,

F

F

F

.:

h

i

h

i

C

h

i

for

reducible

to both

and

L

" d

" d

:

.

.

,

,

F

F

h

i

h

i

For more results and references on Halldoen completeness consult [Chagrov

and Zakharyaschev 1991].

3 POLYMODAL LOGICS

So far we have confined ourselves to considering modal logics with only one

necessity operator. From a theoretical point of view this restriction is not

such a great loss as it may seem at first sight.

In fact. really important

concepts of modal logic do not depend on the number of boxes and can

be introduced and investigated on the basis of just one. We shall give a

precise meaning to this claim in Section 3.2 below where it is shown that

polymodal logic is reduced in a natural way to unimodal logic. However.

there are at least two reasons for a detailed discussion of polymodal logic

in this chapter.

First. a number of interesting phenomena are easily missed in unimodal

logic and actually appear in a representative form only in the polymodal

case. For example. with the exception of NExt

and

all known

K,.5

general decidability results in unimodal logic have been obtained by proving

QC SF

the finite model property.

In fact. nearly all natural classes of logics in

NExt

turned out to be describable by their finite frames. The situation

K

drastically changes with the addition of just one more box. Even in the

case of linear tense logics or bimodal provability logics one has to start with

.

By reductions that map

to

8

d

d

i

ADVANCED MODAL LOGIC

?'

a thorough investigation of their infinite frames: FMP becomes a rather

rare guest. While the result on NExt

indicated the need for general

K,.5

methods of establishing decidability without FMP. this need becomes of

vital importance only in the context of polymodal logic.

The second reason is that various applications of modal logic require

polymodal languages. For example. in tense logic we have two necessity-

like operators

and

. One of them. say the former. is interpreted as "it

.

,

.

.

will always be true" and the other as "it was always true". Kripke frames for

tense logics are structures

W" R

" R

with two binary relations R

and R

.

,

.

,

such that R

coincides with the converse R

of R

(which reflects the fact

5

,

.

.

h

i

.

that a moment x is earlier than y iff y is later than x). The characteristic

axioms connecting the two tense operators are

p

p and p

p.

.

,

,

.

.

,

.

,

.

.

For more information about tense systems consult

Basic Tense Logic

.

Another example is basic temporal logic in which we have two necessity-

like operators: one of them—usually called

—is interpreted by the

Next

successor relation in ' and the other by its transitive and reflexive clo-

sure. Details can be found in [Segerberg 1969]. Propositional dynamic logic

PDL

PDL

and its extensions. like deterministic

. can also be regarded as

polymodal logics (see

).

Dynamic Logic

A number of provability logics use two or more modal operators4 see e.g.

Boolos [1992]. In

. for instance. we have one operator

understood

GLB

.

.

as provability in PA and another operator

interpreted as ' -provability

,

.

in PA. The unimodal fragments of

coincide with

. The axioms

GLB

GL

connecting

and

are

.

,

.

.

.

.

,

.

,

.

,

.

,

.

p

p and

p

p.

.

.

In epistemic logics we need an operator

for each agent i4

. is inter-

i

i

.

.

preted as "agent i believes (or knows) .". One possible way to axiomatize

the logic of knowledge with m agents is to take the axioms of

for each

S.

agent without any principles connecting different

and

. We denote

i

j

.

.

the resultant logic by

. Often

is extended by the common

S.

S.

i

5.

i

5.

m

m

knowledge operator

with the intended meaning

C

N

N

C

E

E

E

E

. ⊆

.

.

. . .

.

. . . " where

. ⊆

,

n

.

.

.

.

m

.

i

.

i

5.

V

(see e.g. [Halpern and Moses 1993] and [Meyer and van der Hoek 1997]).

The reader will find more items for this list in other chapters of the

Handbook.

From the semantical point of view. many standard polymodal logics

can be obtained by applying Boolean or various natural closure opera-

tors to the accessibility relations of Kripke frames. For instance. in frames

fl[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

W" R

" . . . " R

for epistemic logic the common knowledge operator is in-

.

n

h

i

terpreted by the transitive closure of R

. . .

R

. Tense frames result

.

n

from usual

W" R

by adding the converse of R. Humberstone [1962] and

6

6

Goranko [1990a] study the bimodal logic of

determined

inaccessible worlds

h

i

by frames of the form

W" R" W

R

. This list of examples can be con-

,

tinued4 for a general approach and related topics consult [Goranko 1990b].

.

:

[

[Gargov

1968]. [Gargov and Passy 1990].

et al:

Let us see now how polymodal logics in general ,t into the theory de-

veloped so far. We begin by demonstrating how the concepts introduced in

the unimodal case transfer to polymodal logic and showing that a few gen-

eral results—like Sahlqvist's and Blok's Theorems—have natural analogues

in polymodal logic. We hope to convince the reader that up to this point

no new difficulties arise when one switches from the unimodal language to

the polymodal one. After that. in Section 3.3. we start considering subtler

features of polymodal logics.

.,. From unimodal to polymodal

Let

be the propositional language with a finite number of necessity op-

I

L

.

erators

. i

I . A

in

is a set of

-formulas

normal polymodal logic

i

I

I

containing all classical tautologies. the axioms

(p

q)

(

p

q)

i

i

i

.

.

.

?

L

L

for all i

I . and closed under substitution. modus ponens and the rule of

.

.

.

necessitation .,

. for every i

I . If the language is clear from the con-

i

?

.

?

text. we call these logics just (

)

and denote by NExtL

normal

modal logics

the family of all normal extensions of L (in the language

). The smallest

I

L

normal modal logic with n necessity operators is denoted by

(

⊆

.

K

K

K

n

.

of course).

Given a logic L

in

and a set of

-formulas Φ. we again denote by

.

I

I

L

Φ the smallest normal logic (in

) containing L

Φ. A number

.

.

I

L

L

"

L

6

of other notions and results also transfer in a rather straightforward way.

e.g. Theorems 1.5 and 1.6. Proposition 1.7 and all concepts involved in their

formulations. More care has to be taken to generalize Theorems 1.1. 1.3 and

1.2. Denote by

the set of non-empty strings (words) over

: i

I

i

M

.

I

.

which do not contain any

twice and put

i

.

f

?

g

.

.

.

I

. ⊆

. :

"

. ⊆

. : n

m

.

M

M

M

.

,

I

I

I

m

n

f

?

g

f

7

g

.

.

In the language

the operator

serves as a sort of surrogate for

in

I

I

.

.

K

. For example. the following polymodal version of Theorem 1.1 holds.

L

THEOREM 3.1 (Deduction)

L

For every modal logic

in

. every set of

I

L

I

I

5formulas

. and al l

5formulas

and

Φ

.

:

.

L

L

Φ" :

.

.

i,

m

0 Φ

.

:

.

L

L

I

m

.

,

"

1

9

"

.

ADVANCED MODAL LOGIC

fl5

Theorems 1.3 and 1.2 can be reformulated analogously by replacing

.

with

(a logic L in

is n

if it contains

p

p).

5transitive

I

I

,

.

.

.

I

I

n

n

".

L

.

Basic semantic concepts are lifted to the polymodal case in a straight-

forward manner. The algebraic counterpart of L

NExt

is the vari-

n

K

ety of Boolean algebras with n unary operators validating L. A structure

?

F

⊆

W"

R

: i

I

" P

is called a (

general polymodal

frame

)

whenever

i

h

h

?

i

i

every

W" R

" P

. for i

I . is a unimodal frame. We then put

i

h

i

?

.

i

i

X ⊆

x

W :

y (xR

y

y

X )

.

f

?

)

.

?

g

Difierentiated

re.ned

descriptive frames

.

and

and the truth-preserving op-

erations can also be defined in the same component-wise way. For instance.

a frame

⊆

W"

R

: i

I

" P

is differentiated if all the unimodal frames

i

F

W" R

" P

. for i

I . are differentiated.

⊆

W"

R

: i

I

" P

is a (

gen5

i

i

F

h

h

?

i

i

h

i

?

h

h

?

i

i

erated

subframe

)

of

⊆

V "

S

: i

I

" Q

if all

W" R

" P

are (generated)

i

i

G

subframes of

V " S

" Q

. and f is a

of

to

if f is a reduction of

reduction

i

F

G

h

h

?

i

i

h

i

W" R

" P

to

V " S

" Q

. for every i

I .

i

i

h

i

h

i

h

i

?

There are some exceptions to this rule. A point r is called a root of

if it

F

is a root of the unimodal frame

W"

R

. This does not mean that r is a

i

I

i

h

:

i

F

root of all unimodal reducts of

. Another important exception: as before.

S

"

a polymodal frame is

-

if the algebra

is

-generated4 however.

.

generated

F

.

this does not mean that the unimodal reducts of

are

-generated.

F

.

Splittings and the degree of Kripke incompleteness

The semantic

criterion of splittings by finite frames given in Theorem 1.17 transfers to

polymodal logics by replacing

with

. Again. all finite rooted frames

I

.

.

split NExtL

. if L

is an n-transitive logic in

. Notice. however. that

.

.

I

L

n-transitivity is a rather strong condition in the polymodal case. For ex-

ample. it is easily checked that the fusion

as well as the minimal

S.

S.

tense logic

.t containing

are not n-transitive. for any n 5 ' (see

K,

K,

&

Sections 3.3 and 3.5 for precise definitions). In fact. only

splits the lattice

NExt(

) and only

splits NExt

.t (see [Wolter 1992] and [Kracht

S.

S.

K,

o

1993]. respectively).

&

5

Call a frame

W"

R

: i

I

if the unimodal frame

W"

R

cycle free

i

i

i

I

is cycle free. Kracht [1990] showed that precisely the finite cycle free frames

S

h

h

?

ii

h

:

i

split NExt

.

n

K

It is not difficult now to extend Blok's result on the degree of Kripke

incompleteness to the polymodal case. Note. however. that the degree of

incompleteness of

in NExt

is 3

whenever n

3. So. we do not have

For

K

n

"

.

a polymodal analog of Makinson's Theorem. (An example of an incomplete

9

maximal consistent logic in NExt

is the logic determined by the tense

K

,

frame

(0"

) introduced in Section 3.7).

C

o

flff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 3.3

n " 1

L

Let

: If

is a unionffisplitting of

NExt

. then

is

L

K

n

strictly Kripke complete: Otherwise

has degree of Kripke incompleteness

L

.

3

NExt

in

"

K

n

:

Sahlqvist?s Theorem and persistence

The proof of the following poly-

modal version of Sahlqvist's Theorem is a straightforward extension of the

proof in the unimodal case. Say that . is a

(in

) if the

Sahlqvist formula

I

L

result of replacing all

and

. i

I . in . with

and

. respectively. is

i

i

.

,

.

,

a unimodal Sahlqvist formula.

?

THEOREM 3.2

.

NExt

Suppose that

is equivalent in

to a Sahlqvist for5

K

n

mula: Then

K

n

.

is

5persistent. and one can efiectively construct a .rst

order formula

in

and

such that. for every descriptive or

8(x)

R

" . . . " R

⊆

.

n

"

D

Kripke frame

and every point

in

.

i,

:

a

(

" a)

⊆ .

⊆ 8(x)[a]

F

F

F

F

j

j

Bellissima's result on the

-persistence of all logics in NExt

has

n

Alt

a polymodal analog as well. Denote by

the smallest polymodal

Alt

DF

i

I

n

:

logic in

containing

in all its unimodal fragments. It is easy to see

I

n

Alt

N

that every L

NExt

is

-persistent and so Kripke complete.

Alt

i

I

n

L

However. in contrast to the lattice NExt

—which is countable and all

Alt

N

.

?

:

DF

logics in which have FMP (see [Segerberg 1966] and [Bellissima 1966])—

the lattice NExt(

) is rather complex: as was shown by Grefe

Alt

Alt

.

.

[1995]. it contains logics without FMP (even without finite frames at all)

&

and uncountably many maximal consistent logics.

Some FMP results

Fine's Theorem on uniform logics can be extended

to a suitable class of polymodal logics in

. namely those logics that con-

I

L

tain

. for all i

I . and are axiomatizable by formulas . in which all

i

,

maximal sequences of nested modal operators coincide with respect to the

]

?

distribution of the indices i of

and

. i

I .

i

i

.

,

?

Now consider a result of Lewis [1985] which we have not proved in its

unimodal formulation. Call a normal polymodal logic

if it is

nonffiiterative

axiomatizable by formulas without nested modalities. Examples of non-

iterative logics are

⊆

p

p.

and

p

p.

T

K

Alt

Alt

K

m

n

,

,

.

.

.

.

"

.

&

"

.

THEOREM 3.5 (Lewis 1985)

Al l nonffiiterative normal logics have FMP:

Proof

K

Suppose the axioms of L ⊆

Φ have no nested modal oper-

n

ators and .

L. By a .-

we mean any set of subformulas of

description

"

. together with the negations of the remaining formulas in

. For

Sub

'?

each L-consistent .-description % select a maximal L-consistent set

(

containing %. Denote by W the (finite) set of the selected

and define

(

ADVANCED MODAL LOGIC

fl—

F

M

F

V

⊆

W"

R

: i

I

and

⊆

"

by taking

i

h

h

?

ii

h

i

(

)

(

R

iff

&

i

i

,

?

.

and

(p) ⊆

W : p

. It is easily proved that (

"

)

⊆ : iff

(

(

(

V

M

:

. for all subformulas : of . and

W . Hence

⊆ . It is also

(

(

F

f

?

?

g

j

?

?

'j

easy to see that for all truth-functional compounds : of subformulas in .

M

,

,

(

"

)

⊆

: iff

:

.

(15)

(

(

i

i

j

?

Consider now a model

⊆

"

and ?

Φ. For each variable p put

.

.

M

F

V

h

i

?

:

⊆

% :

(p)

p

(

V

"

.

n

o

?

and denote by ?

the result of substituting :

for p. for each p in ?. Then

.

p

M

M

M

.

.

.

.

⊆ ? iff

⊆ ?

. In view of (15). we have

⊆ ?

because ?

has no

j

j

j

nested modalities. Therefore.

⊆ ? and so

⊆ L.

F

F

.

j

j

Tabular Logics

Needless to say that all polymodal tabular logics are

finitely axiomatizable and have only finitely many extensions. (The proof is

the same as in the unimodal case.) A more interesting observation concerns

the complexity of polymodal logics whose unimodal fragments are tabular

or pretabular. In fact. it is not difficult to construct two tabular unimodal

logics L

and L

such that their fusion L

L

has uncountably many

.

,

.

,

normal extensions (see e.g.

[Grefe 1995]). However. those logics are

-

&

persistent and so Kripke complete. Wolter [1995b] showed that the lattice

DF

NExt

can be embedded into the lattice NExt(Log

) in such a way

T

S.

o

"

that properties like FMP. decidability and Kripke completeness are reflected

o

&

under this embedding. It follows that almost all "negative" phenomena of

modal logic are exhibited by bimodal logics one unimodal fragment of which

is tabular and the other pretabular.

.,. Fusions

The simplest way of constructing polymodal logics from unimodal ones is

to form the

(alias

) of them. Namely. given two

fusions

independent joins

unimodal logics L

and L

in languages with the same set of variables and

.

,

distinct modal operators

and

. respectively. the

L

L

of

fusion

.

,

.

,

.

.

L

and L

is the smallest bimodal logic to contain L

L

.

If Φ

and

.

,

.

,

.

&

Φ

axiomatize L

and L

. then L

L

is axiomatized by Φ

Φ

. i.e.

,

.

,

.

,

.

,

6

L

L

⊆

Φ

Φ

. So the fusions are precisely those bimodal logics

K

.

,

,

.

,

&

6

&

"

"

that are axiomatizable by sets of formulas each of which contains only one

fl(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

.

.

of

.

. From the model-theoretic point of view this means that a frame

.

,

W" R

" R

" P

validates L

L

iff

W" R

" P

⊆ L

for i ⊆ 1" 3.

.

,

.

,

i

i

h

i

&

h

i j

PROPOSITION 3.7 (Thomason 1960)

L

L

If logics

and

are consistent.

.

,

then

is a conservative extension of both

and

:

L

L

L

L

.

,

.

,

&

Proof

Suppose for definiteness that .

L

. for some formula . in the

.

'?

language of L

. and consider the Tarski!Lindenbaum algebras

.

A

A

L

.

.

L

:

,

(') ⊆

A"

"

"

and

(') ⊆

B "

"

"

.

.

.

A

A

B

B

.

-

.

-

.

:

.

:

The Boolean reducts of them are countably infinite atomless Boolean alge-

bras which are known to be isomorphic (see e.g.

[Koppelberg 1966]). So

we may assume that A ⊆ B .

⊆

.

⊆

. Since

(') refutes .

A

L

.

A

B

A

B

A

A

.

.

-

-

A"

"

"

"

is then an algebra for L

L

refuting .

.

,

.

,

.

.

.

.

-

&

.

:

Having constructed the fusion of logics. it is natural to ask which of

their properties it inherits. For example. the first order theory of a single

equivalence relation has the finite model property and is decidable. but the

theory of two equivalence relations is undecidable and so does not have the

finite model property (see [Janiczak 1972]). So neither decidability nor the

finite model property is preserved under joins of first order theories. On

the other hand. as was shown by Pigozzi [1985]. decidability is preserved

under fusions of equational theories in languages with mutually disjoint sets

of operation symbols.

For modal logics we have:

THEOREM 3.6

L

L

Suppose

and

are normal unimodal consistent logics

.

,

and

is one of the fol lowing properties" FMP. ?strong" Kripke complete5

P

ness. decidability. Hal ld)en completeness. interpolation. uniform interpola5

tion: Then

has

i, both

and

have

:

L ⊆ L

L

L

L

.

,

.

,

&

P

P

Proof

We outline proofs of some claims in this theorem4 the reader can

consult [Fine and Schurz 1996]. [Kracht and Wolter 1991]. and [Wolter

1998b] for more details.

The implication (

) presents no difficulties. So let us concentrate on

(

). With each formula . of the form

: we associate a new variable

i

8

.

⊆

q

which will be called the

of . For a formula . containing

surrogate

5

,

no surrogate variables. denote by .

the formula that results from . by

replacing all occurrences of formulas

: . which are not within the scope

,

.

of another

. with their surrogate variables q

. So .

is a unimodal

,

"

:

.

.

,

formula containing only

. Denote by %

(.) the set of variables in .

.

.

,

together with all subformulas of

:

. The formula .

and the set

.

Sub

.

.

%

(.) are defined symmetrically.

,

?

ADVANCED MODAL LOGIC

fl)

Suppose now that both L

and L

are Kripke complete and .

L. To

.

,

prove the completeness of L we construct a Kripke frame for L refuting

'?

. Since we know only how to build refutation frames for the unimodal

fragments of L. the frame is constructed by steps alternating between

.

.

and

. First. since L

is complete. there is a unimodal model

based

,

.

M

.

,

on a Kripke frame for L

and refuting .

at its root r. Our aim now is

.

to ensure that the formulas of the form

: have the same truth-values as

,

.

their surrogates q

. To do this. with each point x in

we can associate

.

M

"

:

the formula

.

⊆

:

%

(.) : (

" x)

⊆ :

: : :

%

(.)" (

" x)

⊆ :

"

x

M

M

,

,

,

,

f

?

j

g .

f-

?

'j

g

.

.

construct a model

based on a frame for L

and satisfying .

at its

x

,

x

M

.

root y . and then hook

to

by identifying x and y . After that we can

x

M

M

switch to

and in the same manner ensure that formulas

: have the

.

.

.

.

same truth-values as q

at all points in every

. And so forth.

"

.

x

.

M

However. to realize this quite obvious scheme we must be sure that .

x

is really satisfiable in a frame for L

. which may impose some restrictions

,

on the models we choose. First. one can show that in the construction

above it is enough to deal with points x accessible from r by at most m ⊆

md(.) steps. Let X be the set of all such points. Now. a sufficient and

necessary condition for .

to be L- (and so L

-) consistent can be formulated

x

,

,

as follows. Call a %

(.)-

the conjunction of formulas in any

description

,

,

maximal L-consistent subset of %

(.)

: : :

%

(.)

. It should be

clear that .

is L-consistent iff it is a %

(.)-description. Denote by #

(.)

x

.

,

,

6 f-

?

g

the set of all %

(.)-descriptions.

It follows that all .

. for x

X . are

x

L-consistent iff (

" r)

⊆

(

#

(.))

. In other words. we should start

.

.

M

,

.

m

,

?

with a model

satisfying .

(

#

(.))

at its root r. Of course.

M

.

,

W

.

.

j

,

,

m

the subsequent models

. for x

X . must satisfy .

(

#

(.

))

.

x

W

,

x

x

,

M

.

,

.

.

.

m

.

?

.

where #

(.

) is the set of all %

(.

)-descriptions. etc.

,

x

x

W

In this way we can prove that Kripke completeness is preserved under

fusions. The preservation of strong completeness and FMP can be estab-

lished in a similar manner. The following lemma plays the key role in the

proof of the preservation of the four remaining properties.

LEMMA 3.8

The fol lowing conditions are equivalent for every

.

"

(i) .

L

L

'

.

,

?

m

&

,

,

(ii)

(

#

(.))

.

L

m ⊆ md(.)

. where

'

.

.

.

,

.

.

,

m

.

.

.

?

(iii)

(

#

(.))

.

L

,

W

,

:

,

W

.

?

For Kripke complete L

and L

this lemma was first proved by Fine and

.

,

Schurz [1996] and Kracht and Wolter [1991]4 actually. it is an immediate

consequence of the consideration above. The proof for the arbitrary case is

fl0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

also based upon a similar construction combined with the algebraic proof

of Proposition 3.74 for details see [Wolter 1998b].

Now we show how one can use this lemma to prove the preservation

of the remaining properties. Define a

(.) to be the length of the longest

.

sequence

"

"

" . . . of boxes starting with

such that a subformula

,

.

,

,

.

.

.

.

of the form

(. . .

(. . .

(. . . . . .))) occurs in . The function a

(.) is

,

.

,

.

.

.

,

defined analogously by exchanging

and

. and a(.) ⊆ a

(.) " a

(.).

.

,

.

.

.

,

It is easy to see that

a(.) " a(

#

(.)) or a(.) " a(

#

(.)).

.

,

"

"

The preservation of decidability. Halldoen completeness. interpolation. and

uniform interpolation can be proved by induction on a(.) with the help

of Lemma 3.8. We illustrate the method only for Halldoen completeness.

Notice first that. modulo the Boolean equivalence. we have

#

(.

:) ⊆

#

(.)

#

(:)

 (." :)"

.

.

.

"

"

"

.

,

.

.

where

 (." :) ⊆

?

?

: ?

#

(.)" ?

#

(:)" ?

?

L

.

.

,

.

.

,

.

.

,

f

. -

?

?

. -

?

g

Suppose both L

and L

are Halldoen complete. By induction on n ⊆ a(.

:)

.

,

we prove that .

:

L implies .

L or :

L whenever . and : have no

,

common variables. The basis of induction is trivial. So suppose a(.

:) ⊆

,

?

?

?

n " 0 and .

:

L. We may also assume that a(.

:) " a(

#

(.

:)).

.

,

By the induction hypothesis. it follows that  (." :) ⊆

. Hence. up to the

,

?

,

,

W

fl

Boolean equivalence.

#

(.

:) ⊆

#

(.)

#

(:) and. by Lemma 3.8.

.

.

.

,

.

W

W

W

m

m

,

,

,

.

.

,

,

(

#

(.))

(

#

(:))

(.

:)

L

"

.

.

.

.

.

"

"

.

.

,

?

for m ⊆ md(.

:). Then

,

m

m

,

,

,

,

.

.

(

(

#

(.))

.

)

(

(

#

(:))

:

)

L

,

,

.

.

.

.

.

"

"

.

,

.

?

and. by the Halldoen completeness of L

. one of the disjuncts in this formula

.

belongs to L

. By Lemma 3.8. this means that .

L or :

L.

.

.

?

?

Remark.

This theorem can be generalized to fusions of polymodal logics

with polyadic modalities.

Note that in languages with finitely many variables both

.

and

GL

5

K

are strongly complete but

.

is not strongly complete even in the

GL

5

K

language with one variable (see [Kracht and Wolter 1991]).

&

ADVANCED MODAL LOGIC

fl?

It is natural now to ask whether there exist interesting axioms . contain-

ing both

and

and such that (L

L

)

. inherits basic properties of

.

,

.

,

.

.

L

" L

NExt

. Let us start with the observation that even such a simple

K

.

,

&

"

axiom as

p

p destroys almost all "good" properties because (i) we

.

,

?

.

.

can identify (L

L

)

p

p with the sum of the translation of L

.

,

.

,

.

5

.

.

and L

into a common unimodal language and (ii) such properties as FMP.

,

&

"

5

decidability. and Kripke completeness are not preserved under sums of uni-

modal logics (see Example 1.65 and [Chagrov and Zakharyaschev 1998]).

Even for the simpler formula

p

p no general results are available.

,

.

.

.

To demonstrate this we consider the following way of constructing a bimodal

.

logic L

for a given L

NExt

:

u

K

?

L

⊆ (L

)

p

p.

u

,

.

S.

.

.

&

"

.

The modal operator

in L

is called the

. Its meaning

universal modality

,

u

.

is explained by the following lemma:

LEMMA 3.6 (Goranko and Passy 1993)

L

For every normal unimodal logic

and al l unimodal formulas

and

.

:

.

.

.

:

i,

.

: .

L

L

u

,

.

"

"

.

Proof

Follows immediately from Theorem 1.19 (ii). since

W" R" P

⊆ L iff

W" R" W

W" P

⊆ L

"

u

h

i j

h

’

i j

for every frame

W" R" P

and every unimodal logic L.

.

h

i

The universal modality is used to express those properties of frames

⊆

F

W" R" W

W

that cannot be expressed in the unimodal language. For

h

’

i

F

.

,

example.

validates

(p

p)

p iff it contains no infinite R-

,

.

chains. Recall that there is no corresponding unimodal axiom. since

is

K

.

. -

determined by the class of frames without infinite R-chains. We refer the

reader to [Goranko and Passy 1993] for more information on this matter.

THEOREM 3.9 (Goranko and Passy 1993)

L

NExt

For any

K

.

(i) L

L

u

is global ly Kripke complete i,

is Kripke complete'

?

(ii) L

L

u

has global FMP i,

has FMP:

Proof

We prove only (i). Suppose that L

is Kripke complete and .

: .

u

.

L

'"

Then by Lemma 3.6.

.

:

L

and so

.

: is refuted in a Kripke

,

,

u

.

.

frame

⊆

W" R

" R

for L

. We may assume that R

⊆ W

W . But

.

,

,

u

F

.

'?

.

then .

: is refuted in

W" R

. Conversely. suppose that L is globally

.

L

.

h

i

’

Kripke complete and .

L

. for a (possibly bimodal) formula . Using

u

"

h

i

'?

flfl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

the properties of

it is readily checked that . is (effectively) equivalent

S.

in

to a formula .

which is a conjunction of formulas : of the form

u

.

K

: ⊆ ?

?

?

?

. . .

?

.

,

.

,

,

,

:

,

n

,

.

.

.

,

,

,

,

,

such that ?

" . . . " ?

are unimodal formulas in the language with

. Let

.

n

.

.

: be a conjunct of .

such that :

L

. Then

?

?

. for every

.

u

.

.

i

L

i

0" 3" 2" . . . " n

. Since L is globally complete. we have Kripke frames

'?

-

'"

? f

g

W

" R

for L refuting

?

?

. for i

0" 3" . . . " n

. Denote by

W" R

i

i

.

.

i

L

h

i

-

"

? f

g

h

i

the disjoint union of those frames. Then

W" R" W

W

is a Kripke frame

for L

refuting .

u

h

’

i

.

We have seen in Section 1.7 that there are Kripke complete logics (logics

with FMP) which do not enjoy the corresponding global property. In view

of Theorem 3.9. we conclude that neither FMP nor Kripke completeness is

preserved under the map L

L

.

u

".

Another interesting way of adding to fusions new axioms mixing the

necessity operators is to use the so called

(or

)

.

inductive

Segerberg1s

axioms

First. we extend the language

with m necessity operators by introducing

the operators

and

and then let

E

C

I

L

ind

E

C

EC

C

E

C

⊆

p

p"

p

p4

(p

p)

(p

p)

.

i

.

f

5

.

.

.

.

g

i

I

.

:

Now. given L

NExt

. we put

m

K

?

L

⊆ (L

)

"

m

EC

K

S,

ind

E

C

&

&

"

where

and

are just

and

in the languages with

and

. re-

K

S,

K

S,

E

C

E

C

spectively. The following proposition explains the meaning of the inductive

axioms.

PROPOSITION 3.10

W" R

" . . . " R

" R

" R

A frame

validates

L

EC

.

m

E

C

m

i,

.

and

is the transitive

W" R

" . . . " R

⊆ L

R

⊆ R

. . .

R

R

.

.

m

E

m

C

h

i

h

i j

6

6

re—exive closure of

:

R

E

EXAMPLE 3.11 The logic (

)

is determined by the frame

Alt

D

EC

.

.

' " S"

in which S is the successor relation in ' .

(Here we omit writ-

"

h

7i

.'

ing R

because R

⊆ S .) For details consult [Segerberg 1969].

E

E

No general results are known about the preservation properties of the

map L

L

. In fact. it is easy to extend the counter-examples for the

m

EC

map L

L

to the present case (see [Hemaspaandra 1996]). However. at

u

".

least in some cases—especially those that are of importance for epistemic

".

logic—the logic L

enjoys a number of desirable properties.

m

EC

.:

Krister Segerberg kindly informed us that this result was independently obtained by

D8 Scott- H8 Kamp- K8 Fine and himself8

ADVANCED MODAL LOGIC

fl'

THEOREM 3.13 (Halpern and Moses 1993)

m

1

For every

. the logics

m

m

m

9

(

)

m

.

(

)

and

(

)

have FMP:

m

m

K

EC

S,

EC

S.

EC

i

5.

i

5.

i

5.

N

N

N

m

Proof

S.

EC

We consider only L ⊆ (

)

. The proof is by filtration

i

5.

m

and so the main difficulty is to find a suitable "filter". Suppose that .

L

N

and let

⊆

W" R

" . . . " R

" R

" R

"

be the canonical model for L.

.

m

E

C

M

U

'?

Denote by Φ

the closure of a set of formulas Φ under negations and define

9

hh

i

i

a filter ’ ⊆ ’

’

’

. where ’

⊆

. ’

⊆

: :

:

’

9

9

9

i

9

.

,

Sub

E

.

,

:

.

.

and ’

⊆

: "

: :

:

’

. Certainly. ’ is finite and closed under

:

i

9

.

EC

C

C

.

6

6

f

?

g

subformulas. Now. we filter

through ’. i.e. put W

⊆

[x] : x

W

.

.

M

f

?

g

where [x] consists of all points that validate the same formulas in ’ as x.

f

?

g

and

[x]R

[y ] iff

:

’ ((

" x)

⊆

:

(

" y)

⊆

:)"

i

i

i

i

.

.

.

M

M

)

?

j

.

j

R.

⊆ R.

. . .

R.

"

E

m

.

6

6

and R

is the transitive and reflexive closure of R

. A rather tedious

.

C

.

E

inductive proof shows that

W

" R

" . . . " R

" R

" R

refutes . under the

.

.

.

.

.

.

m

E

C

valuation

(p) ⊆

[x] : x

⊆ p

. p a variable in . For details we refer the

.

U

h

i

reader to [Halpern and Moses 1993] and [Meyer and van der Hoek 1997].

f

j

g

.

It would be of interest to look for big classes of logics L for which L

EC

m

inherits basic properties of L.

.,: Simulation

In the preceding section we saw how results concerning logics in NExt

can

K

be extended to a certain class of polymodal logics. More generally. we may

ask whether—at least theoretically—polymodal logics are reducible to uni-

modal ones. The first to attack this problem was Thomason [1985b. 1987c]

who proved that each polymodal logic L can be embedded into a unimodal

logic L

in such a way that L inherits almost all interesting properties of

s

s

L

. Using this result one can construct unimodal logics with various "nega-

tive" properties by presenting first polymodal logics with the corresponding

properties. which is often much easier. It was in this way that Thomason

[1987c] constructed Kripke incomplete and undecidable unimodal calculi.

Kracht [1996] strengthened Thomason's result by showing that his embed-

ding not only reflects but also (i) preserves almost all important properties

and (ii) induces an isomorphism from the lattice NExt

onto the interval

K

,

Sim

K

Sim

[

"

]. for some normal unimodal logic

. Thus indeed. in many

.

respects polymodal logics turn out to be reducible to unimodal ones.

"

:

Below we outline Thomason's construction following [Kracht 1996] and

[Kracht and Wolter 1998a]. To define the unimodal "simulation" L

of a

s

'[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

4

5

'I

AK

A

'

0

.

R

R

.

:

5

5

5

"

"

A

F

F

[

A

[

s

0

.

5

5

5

Figure 11.

bimodal logic L. let us first transform each bimodal frame into a unimodal

one.

So suppose

⊆

W" R

" R

" P

is a bimodal frame. Construct a unimodal

.

,

F

frame

⊆

W

" R

" P

—the

of

—by taking

simulation

F

F

s

s

h

s

s

i

h

i

s

W

⊆ W

1" 3

"

s

’ f

g 6 f4g

R

⊆

x" 1

"

x" 3

: x

W

fhh

i

h

ii

?

g 6

x" 3

"

x" 1

: x

W

fhh

i

h

ii

?

g 6

x" 1

"

: x

W

fhh

i

4i

?

g 6

x" 1

"

y " 1

: x" y

W" xR

y

.

fhh

i

h

ii

?

g 6

x" 3

"

y " 3

: x" y

W" xR

y

"

,

s

fhh

i

h

ii

?

g

P

⊆

(X

3

)

(Y

1

)

Z : X" Y

P" Z

.

f

’ f

g

6

’ f

g

6

?

ff f4gg

This construction is illustrated by Fig. 11. One can easily prove that

is a

s

F

Kripke (differentiated. refined. descriptive) frame whenever

is so. Notice

F

also that if W ⊆

then

. Now. given a bimodal logic L. define the

s

F

simulation

L

of L to be the unimodal logic

s

fl

5

⊆

2

To formulate the translation which embeds L into L

we require the follow-

ing formulas and notations:

s

Log

:

⊆ L

.

F

F

f

j

g

s

( ⊆

. ⊆

((

.)

0

.

.

.

— ⊆

. ⊆

(—

.)

ff

,.

.

.

:

.

] ⊆

(

(

. ⊆

(]

.).

-

:

.

,

.

.

-

. -

.

,

,

,

0

ff

-

.

and

are defined dually. Observe that the formula ( is true in

s

F

only at

. — is true precisely at the points in the set

x" 1

: x

W

.

and ] is true at the points

x" 3

: x

W

and only at them. Put

4

fh

i

?

g

fh

i

?

g

s

p

⊆ p"

s

s

(

.)

⊆ —

.

"

-

. -

s

s

s

(.

:)

⊆ .

:

"

.

s

.

s

.

.

(

.)

⊆

.

"

.

ff

.

.

.

.

(

.)

⊆

.

.

-

-

ff

,

s

s

By an easy induction on the construction of . one can prove

ADVANCED MODAL LOGIC

'5

LEMMA 3.12

⊆

"

X ⊆

x : x

⊆ —

Let

be a bimodal model.

and

M

F

V

s

s

s

s

h

i

f

j

g

let

be a model such that

. for al l

⊆

"

(p)

X ⊆

(p)

1

M

F

V

V

V

variables

: Then for every bimodal formula

p

.

.

h

i

0

’ f

g

M

M

(

" x)

⊆ .

(

"

x" 1

)

⊆ .

"

i,

s

s

j

s

h

i

j

s

M

M

⊆ .

i,

⊆ —

.

"

j

j

.

s

s

F

F

⊆ .

⊆ —

.

.

i,

j

j

.

Using this lemma. both consequence relations

and

can be reduced to

L

.

L

"

s

"

the corresponding consequence relations for L

.

PROPOSITION 3.15

L

Let

be a bimodal logic.

a set of bimodal formulas

and

a bimodal formula: Then

.

L

L

.

—

i,

—

.

"

s

s

s

"

.

s

"

.

s

.

L

.

—

i,

s

.

L

—

.

"

"

.

"

.

where

—

⊆

—

9 : 9

:

s

s

.

f

.

?

g

To axiomatize L

. given an axiomatization of L. we require the following

s

formulas:

(a) —

(

p

p)" —

p

p"

0

0

0

ff

0

,

.

,

.

,

.

5

.

.

(b) —

(

p

p)"

-

-

,

.

.

5

(c) ]

(

p

p)"

ff

ff

,

.

.

5

(d) —

p

p" ]

p

p"

-

ff

ff

-

.

.

.

.

.

.

.

.

(e) —

p

p.

0

-

-

ff

0

,

.

.

.

,

.

.

s

F

Let

⊆

(a)" . . . " (e)

. Obviously.

is a frame for

whenever

Sim

K

Sim

F

F

is a bimodal frame. Consider now a differentiated frame

⊆

W" R" P

" f

g

for

which contains only one point where ( is true. (Actually. every

Sim

h

i

rooted differentiated frame for

satisfies this condition.) Construct a

Sim

bimodal frame

⊆

V " R

" R

" Q

. called the

of

. in the

unsimulation

s

.

,

F

F

following way. Put V ⊆

x

W : x

⊆ —

. V

⊆

x

W : x

⊆ ]

and

0

h

i

U ⊆

x

W : x

⊆ (

. Since (

—

]

. we have W ⊆ V

V

U . It

K

0

f

?

j

g

f

?

j

g

f

?

j

g

,

,

?

6

6

is not hard to verify using (b) and (c) (and the differentiatedness of

) that

F

for every x

V there exists a unique x

V

such that xRx

. and for every

0

0

0

y

V

there exists y

V such that yRy

. By (d). x ⊆ x

. Finally. we

0

-

-

0-

?

?

?

?

,

,

put R

⊆ R

V

. R

⊆

x" y

V

: x

Ry

and Q ⊆

X

V : X

P

.

.

,

0

0

It is easily proved that

is a bimodal frame. The name

is

unsimulation

s

F

0

fh

i ?

g

f

0

?

g

justified by the following lemma.

LEMMA 3.17

For every difierentiated bimodal frame

.

:

(

)

s

⊆

F

F

F

s

2

Now we have:

'ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 3.16

L ⊆

For every bimodal logic

.

K

,

"

s

s

L

⊆

—

.

Sim

"

.

s

s

Proof

Sim

Clearly.

—

L

. Assume that the converse inclusion

does not hold. Then there exists a rooted differentiated

such that

⊆ L

F

F

"

.

ff

s

but

⊆

—

. By Lemma 3.17. (

)

⊆ L

. By the definition

s

F

F

Sim

s

s

s

'j

s

j

"

.

'j

of L

. we then conclude that

⊆ L. And by Proposition 3.15. we have

F

s

'j

s

s

s

F

F

(

)

⊆ —

. from which

⊆ —

.

s

.

'j

.

'j

.

Given L

[

"

]. the logic L

⊆

. : —

.

L

is called the

s

Sim

K

.

s

unsimulation

of L.

?

"

:

f

.

?

g

LEMMA 3.18

L

(

If

is determined by a class

of frames in which

is true

only at one point then

:

L

⊆ Log

:

s

s

F

F

C

f

? C g

We are in a position now to formulate the main result of this section.

THEOREM 3.16 (Kracht 1996)

L

L

The map

is an isomorphism from

s

the lattice

onto the interval

: The inverse map

NExt

[

"

]

K

Sim

K

,

.

".

.

is

L

L

s

: Both these maps preserve tabularity. ?global" FMP. ?global"

"

:

".

Kripke completeness. decidability. interpolation. strong completeness.

5

and

5persistence. elementarity:

D

R

s

Proof

To prove the first claim it suffices to show that (L

)

⊆ L for every

s

L

[

"

]. That L

(L

)

is clear. Consider the set

of all

s

Sim

K

.

s

?

"

:

ff

C

differentiated frames

such that

⊆ L and ( is true only at one point in

s

F

F

F

. By Lemma 3.18.

characterizes L

. It is not difficult to show now that

s

j

the class

:

is closed under subalgebras. homomorphic images

"

C

F

F

s

f

? C g

and direct products4 so it is a variety. Consequently.

is (up to isomorphic

copies) the class of all differentiated frames for L

.

s

C

Take a differentiated frame

for (L

)

. Then

⊆ L

. So there exists

s

s

s

F

F

s

G

s

which is isomorphic to

. Hence (

)

(

)

and

⊆ L. since

s

s

s

⊆

F

F

G

F

s

s

j

? C

s

s

j

2

G

F

F

⊆ L. It follows that L

is determined by

:

whenever L is

j

f

? C g

determined by

.

C

The preservation of tabularity. (global) FMP. (global) Kripke complete-

ness. and strong completeness under both maps is proved with the help of

Lemma 3.18 and the observation above. It is also clear that L is decidable

whenever L

is decidable. For the remaining (rather technical) part of the

s

proof the reader is referred to [Kracht 1996] and [Kracht and Wolter 1998a].

.

Besides its theoretical significance. this theorem can be used to transfer

rather subtle counter-examples from polymodal logic to unimodal logic. For

instance. Kracht [1996] constructs a polymodal logic which has FMP and is

globally Kripke incomplete. By Theorem 3.16. we obtain a unimodal logic

with the same properties.

ADVANCED MODAL LOGIC

'—

.," Minimal tense extensions

Now let us turn to

which may be regarded as normal bimodal

tense logics

logics containing the axioms p

p and p

p. Usually studies

.

,

,

.

.

,

.

,

in Tense Logic concern some special systems representing various models of

.

.

time. like cyclic time. discrete or dense linear time. branching time. rela-

tivistic time. etc. Such systems are discussed in

(see also

Basic Tense Logic

[Gabbay

1995] and [Goldblatt 1968]). However. as before our concern

et al:

is general methods which make it possible to obtain results not only for this

or that particular system but for wide classes of logics. This direction of

studies in Tense Logic is quite new and actually not so many general results

are available. In this and the next section we consider two natural families

of tense logics—the minimal tense extensions of unimodal logics and tense

logics of linear frames. Our aim is to find out to what extent the theory

developed for unimodal logics in NExt

and especially NExt

can be

K

K,

"lifted" to these families.

The smallest tense logic

.t is determined by the class of bimodal Kripke

K

frames

W" R" R

in which R is the accessibility relation for

and R

5

.

5

.

.

.

.

h

i

for

. Frames of this type are known as

4 general frames

tense Kripke frames

,

of the form

W" R" R

" P

will be called just

. Notice that not

tense frames

5

.

all unimodal general frames

W" R" P

can be converted into tense frames

h

i

W" R" R

" P

because P is not necessarily closed under the operation

5

.

h

i

h

i

,

,

X ⊆

x

W :

y

X xR

y

.

5

.

f

?

1

?

g

For instance. in the frame

of Example 1.8 we have

' " 1

⊆

'

P .

,

F

,

Each normal unimodal logic L ⊆

Φ in the language with

gives rise

K

.

f

g

f

g '?

.

to its

L.t ⊆

.t

Φ. From the semantical point of

minimal tense extension

"

K

view L.t is the logic determined by the class of tense frames

W" R" R

" P

5

"

.

such that

W" R" P

⊆ L. The formation of the minimal tense extensions

h

i

is the simplest way of constructing tense logics from unimodal ones. Of

h

i j

"natural" tense logics. minimal tense extensions are. for instance. the logics

of (converse) transitive trees. (converse) well-founded frames. (converse)

transitive directed frames. etc. The main aim of this section is to describe

conditions under which various properties of L are inherited by L.t.

Notice first that unlike fusions. L.t is not in general a conservative ex-

tension of L. witness L ⊆ Log

where

is again the frame constructed in

F

F

Example 1.8: one can easily check that

.t

L.t. However. if L is Kripke

K,

complete then L.t is a conservative extension of L and so L

.t ⊆ L.t implies

.

ff

L

L. This example may appear to be accidental (as the first examples of

.

ff

Kripke incomplete logics in NExt

). However. we can repeat (with a slight

K

modification) Blok's construction of Theorem 1.27 and prove the following

'(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 3.19

L

NExt

L ⊆

If

is a unionffisplitting of

or

. then

K

For

L

.t ⊆ L.t

L

⊆ L

implies

: Otherwise there is a continuum of logics in

.

.

NExt

K

having the same minimal tense extension as

L

:

It is not known whether there exists L

NExt

such that L.t is not a

K,

conservative extension of L.

?

Theorem 3.19 leaves us little hope to obtain general positive results for

the whole family of minimal tense extensions. As in the case of unimodal

logics we can try our luck by considering logics with transitive frames. So in

the rest of this section it is assumed that the unimodal and tense logics we

deal with contain

and

.t. respectively. and that frames are transitive.

K,

K,

But even in this case we do not have general preservation results: Wolter

[1996b] constructed a logic L

NExt

having FMP and such that L.t is

K,

not Kripke complete. However. the situation turns out to be not so hopeless

?

if we restrict attention to the well-behaved classes of logics in NExt

.

K,

namely logics of finite width. finite depth and cofinal subframe logics. First.

we have the following results of [Wolter 1996a].

THEOREM 3.30

L

NExt

L.t

If

is a logic of .nite depth then

has

K,

FMP: If

is a logic of .nite width then

is Kripke complete:

L

NExt

L.t

K,

?

?

It is to be noted that tense logics of finite depth are much more complex

than their unimodal counterparts. For example. there exists an undecidable

finitely axiomatizable logic containing

.t

(for details see [Kracht

.

.

K,

.

.

and Wolter 1998a]).

"

:

The minimal tense extensions of cofinal subframe logics were investigated

in [Wolter 1997. 1996a].

THEOREM 3.31

L

NExt

If

is a co.nal subframe logic then

K,

(i) L.t

is Kripke complete'

?

(ii) L.t

L

has FMP i,

is canonical'

(iii) L.t

L

is decidable whenever

is .nitely axiomatizable:

Before outlining the idea of the proof we note some immediate conse-

quences for a few standard tense logics.

EXAMPLE 3.33 (i) The logic of the converse well-founded tense frames is

GL

.t4 it does not have FMP but is decidable. (ii) The logic of the converse

transitive trees is

.

.t4 it has FMP and is decidable. (iii) The logic of

K,

5

the converse well-founded directed tense frames is

.t

.

.t4 it does

GL

K,

"

not have FMP and is decidable.

"

Proof

The proof of the negative part. i.e. that L.t does not have FMP if

L is not canonical. is rather technical4 it is based on the characterization of

ADVANCED MODAL LOGIC

')

the canonical cofinal subframe logics of [Zakharyaschev 1996]. The reader

can get some intuition from the following example: neither

.t nor

.t

Grz

GL

has FMP. Indeed. the Grzegorczyk axiom

.

.

.

,

,

,

(

(p

p)

p)

p

.

.

.

is refuted in

' "

"

and so does not belong to

.t4 however. it is valid

Grz

in all finite partial orders. The argument for

.t is similar: take the L;ob

GL

h

9

7i

axiom in

and the frame

' " "" 5

.

,

.

h

i

We sketch now the proof of the positive part. For a tense Kripke frame

F

rp

⊆

W" R" R

. let

be a partial function associating with some clusters

5

.

h

i

in

one of the frames

F

' " "" 5

or

' "

"

.

h

i

h

9

7i

We call it a

for

and define

to be the result of

replacement function

F

F

rp

replacing in

all clusters C in the domain of

by (disjoint copies of )

C .

F

rp

rp

Our first observation is that for each cofinal subframe logic L. L.t is de-

termined by a set of frames of the form

such that

is of finite depth.

rp

F

F

Indeed. suppose .

L.t and consider a countermodel

⊆

"

for .

M

F

V

based on a descriptive finitely generated tense frame

⊆

W" R" R

" P

for

5

F

'?

h

i

.

L.t. Say that a point x

W is

(relative to .) if there are a

nonffieliminable

h

i

subformula : of . and S

R" R

such that x

max

y

W : y

⊆ :

5

S

?

.

or x

max

y

W : y

⊆

:

. Denote by W

the set of non-eliminable

S

e

? f

g

?

f

?

j

g

?

f

?

j

-

g

points in W and construct a new model

on the frame

⊆

W

" R

e

e

e

M

F

.

W

" R

W

by taking

(p) ⊆

(p)

W

for all variables p in . Clearly.

e

5

e

e

e

.

.

V

V

h

the Kripke frame

is of finite depth (d(

)

3l(.). to be more pre-

e

e

F

F

i

0

cise). Besides. using Theorem 1.32 one can easily show that (

" y)

⊆ : iff

e

7

M

M

Sub

(

" y)

⊆ : . for all :

. and y

W

. (Note that Theorem 1.32 is ap-

e

j

plicable in this case. since

W" R" P

is descriptive whenever

W" R" R

" P

5

j

?

?

.

is descriptive.) Moreover. the R-reduct

W

" R

W

of

is a cofinal sub-

e

e

e

.

:

.

F

h

i

frame of the R-reduct

W" R

of the underlying Kripke frame of

. So

is

e

F

F

h

i

a frame for L.t whenever L is canonical (⊆

-persistent). However. this is

h

i

not so if L is not canonical.

D

EXAMPLE 3.32 Consider the frame

⊆

W" R" R

" P

. where

W" R

is

5

F

.

the reflexive point

followed by the chain

' " "

and P consists of all

h

i

h

i

cofinite sets containing

and their complements. Then

⊆

.t but (for

F

GL

4

h

i

an arbitrary .)

contains

and so

⊆

.t.

e

e

F

F

GL

4

j

4

'j

A rather tedious proof (see [Wolter 1996a]) shows. however. that there

exists a replacement function

for

such that

validates L.t and all

rp

F

F

e

e

rp

points in clusters from dom

are eliminable relative to R in

. (In the

rp

F

example above we put

⊆

' " "" 5

and

is eliminable relative to

rp

f4g

h

i

4

'0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

R.) So let us assume that such

is given and that its domain is empty if

rp

L is canonical. Define a model

⊆ (

"

) as follows. First we put

e

e

rp

rp

rp

M

F

V

y

(p) whenever y

(p) and y ,

dom

. Consider now a cluster

e

V

V

rp

rp

?

?

rp

?

C ⊆

a

" . . . " a

in dom

.

is defined in

C by unravelling C into

.

.

m

rp

rp

V

f

g

5

the chain

C 4 more precisely. we put

rp

rp

V

V

rp

(p)

C ⊆

mj " i : j 5 ' " a

(p)

.

i

0

f

?

g

Using the fact that dom

contains only R-eliminable points. one can show

rp

by induction that. for every :

. (

" y)

⊆ : iff (

" y)

⊆ : . if

Sub

M

M

e

e

rp

C (y) does not belong to dom

. and

rp

?

j

j

n

C : (

" n)

⊆ :

⊆

mj " i : j 5 ' " (

" a

)

⊆ :

"

e

i

rp

M

M

e

rp

f

?

j

g

f

j

g

if a cluster C ⊆

a

" . . . " a

is in dom

. Thus

refutes . which

.

.

m

e

rp

F

rp

proves that L.t is Kripke complete.

f

g

5

To show that all canonical logics L.t do have FMP we reduce

once

e

rp

F

again. Define an equivalence relation

on W

by induction on the R-depth

e

d

(x) of a point x in

. Suppose that d

(x) ⊆ d

(y) and

is already

R

e

R

R

F

2

defined for all points of R-depth 5 d

(x) and put x

y if the following

R

2

conditions are satisfied: (a) x

⊆ : iff y

⊆ : . for all :

. (x

y . for

5

2

Sub

short). (b) if z is an R-successor of y and C (z )

⊆ C (y) then there exists an

j

j

?

2

R-successor z

of x with C (z

)

⊆ C (x) such that z

z

and vice versa. (c)

.

.

.

the cluster C (x) is degenerate iff C (y) is degenerate. (d)

C (x) ⊆

C (y).

rp

rp

2

(e) for each z

C (x) there exists z

C (y) such that z

z

and vice

.

5

.

versa.

?

?

2

Let [x] denote the equivalence class generated by x. Define a frame

G

.

⊆

V " S" S

by taking V ⊆

[x] : x

W

. and [x]S [y ] iff there are

5

e

h

i

f

?

g

x

[x] and y

[y ] such that x

Ry

. Since

is of finite depth. V is

.

.

.

.

e

F

?

?

finite. Moreover. the map x

[x] is a reduction of the unimodal frame

W

" R

W

to

V " S

. It follows that

is a frame for L.t whenever L is

e

e

.

G

".

h

i

h

i

canonical. Define a valuation in

by putting [x]

⊆ p iff x

⊆ p. for all

G

x

W

and all variables p in . Then one can show that [x]

⊆ : iff x

⊆ : .

e

j

j

?

j

j

for all :

. So

⊆ . as required. which means that L.t has FMP.

Sub

G

?

'j

To prove the decidability of a finitely axiomatizable L.t we first show its

completeness with respect to a rather simple class of frames.

Define a replacement function

for

as follows. For each cluster C in

rf

G

F

e

the set [C ] ⊆

[x] : x

C

is a cluster in

. and moreover. every cluster

G

in

can be presented in this way. So we put

[C ] ⊆

C . for all clusters

G

rf

rp

f

?

g

[C ] in

. Notice that by (d).

is well-defined. It is easily shown now that

G

rf

the R-reduct of

is reducible to the R-reduct of

and that

refutes

F

G

G

e

rp

rf

rf

. Thus we obtain

'
'
ADVANCED MODAL LOGIC

'?

LEMMA 3.35

For each co.nal subframe logic

L

.

L.t ⊆ Log

:

⊆ L.t"

.nite.

a replacement function for

G

G

G

rp

G

.

rp

rp

f

j

g

So. to establish the decidability of a finitely axiomatizable L.t it is enough

now to present an algorithm which is capable of deciding. given an

for a

rp

finite

and . whether

⊆ . To this end we require the notion of a

G

G

rp

cluster assignment

⊆

"

in a tense frame

. which is any function from

t

t

t

G

j

.

,

h

i

the set of clusters in

into the set

"

"

such that

C ⊆ (

"

) if C

G

m

j

m

j

t

m

m

is degenerate (here

and

are just two symbols4

stands for "maximal"

m

j

m

f

g’ f

g

and

for "joker"). A valuation

in

is called .-

(

"

) if the

good for

j

V

G

G

t

following conditions hold:

if

C ⊆

then C

max

(

(:)) ⊆

. for all :

.4

t

j

Sub

V

.

R

5

0

fl

?

if

C ⊆

then C

max

(

(:)) ⊆

. for all :

. .

t

j

Sub

,

R

"

.

V

5

0

fl

?

EXAMPLE 3.37 Let

be the frame constructed in Example 3.32 and sup-

F

pose that

⊆ (

"

). Then each valuation

in

is .-good for (

"

)

t

j

m

t

V

F

G

no matter what . is. because

is eliminable relative to R. The point

f4g

.

4

4

is not R

-eliminable. since

max

(

).

5

R

"

.

4 ?

]

Given a formula . a finite frame

and a replacement function

for

F

rp

F

G

. we construct a finite frame

⊆

V " S" S

with a cluster assignment

5

.

t

as follows. Let k be the number of variables in . Then

is obtained

G

h

i

from

by replacing every

C ⊆

' " "" 5

with a non-degenerate cluster

rp

rp

F

C

of cardinality 3

. S -followed by a chain of 3l(.) irreflexive points. and

.

k

h

i

by replacing every

C ⊆

' "

"

with a non-degenerate cluster C

of

rp

.

cardinality 3

. S -followed by a chain of 3l(.) reflexive points. The cluster

k

h

9

7i

assignment

in

is defined by putting

C

⊆ (

"

). for all new clusters

.

t

t

j

m

G

C

of cardinality 3

. and

C

⊆ (

"

). for all the other clusters.

It is

.

.

t

m

m

k

not difficult now to prove that

⊆ . iff (

"

)

⊆ . for all .-good for

rp

F

G

U

G

U

G

t

(

"

) valuations

in

. This equivalence provides an effective procedure

j

j

for deciding whether

⊆ .

rp

F

j

.

Note that a similar technique can be used to prove completeness and

decidability of various tense logics that are not minimal tense extensions.

For instance. all logics of the form L.t

p

p. where L is a

,

,

,

,

,

.

.

,

cofinal subframe logic. are complete and decidable if finitely axiomatizable.

"

.

.,5 Tense logics of linear frames

One of the most important types of tense logics are logics characterized

by linear tense frames. i.e. transitive frames

W" R" R

" P

such that. for

5

.

.

:

'fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

all x" y

W . xRy or xR

y or x ⊆ y . For example. Bull [1966] and

5

.

Segerberg [1980] axiomatized the logics of the frames.

" 5" "

.

" 5" "

Z

Q

?

and

" 5" "

(

.

and

are the sets of integer. rational and real numbers.

R

Z

Q

R

h

i

h

i

h

i

respectively).

Linear tense logics

form the lattice NExt

. where

Lin

Lin

K,

⊆

.t

p

p

p

p

p

.

,

,

.

.

,

,

,

,

,

,

,

"

,

.

,

,

is the tense logic determined by the class of all linearly ordered Kripke

frames

W" R" R

. As we saw in Section 1.11. even unimodal logics of

5

.

linear orders are rather non-trivial (for instance. they do not always enjoy

.

:

FMP). Yet they can be characterized by Kripke frames with a transpar-

ent structure. which yields a decision algorithm for those of them that are

finitely axiomatizable. Tense logics of linear frames turn out to be even more

complicated. In fact. one can find almost all kinds of "monsters" among

them: uncountably many logics without Kripke frames. strongly complete

logics that are not canonical. canonical logics that are not

-persistent.

incomplete subframe logics. etc. Nevertheless. in this section we show that

R

these logics are quite manageable. Our exposition follows [Wolter 1996c.d].

where the reader can find the omitted details. All frames in this section are

assumed to be linear.

Given a finite sequence

⊆

⊆

W

" R

" P

: 1

i

n

of disjoint

i

i

i

i

F

F

frames. we denote by [

] ⊆

. . .

the ordered sum of them. i.e. the

.

n

F

F

F

.

.

h

h

i

7

7

i

frame

W" R" R

" P

in which

5

.

.

:

n

n

W ⊆

W

" R ⊆

R

(W

W

)

i

i

i

j

i

5.

5

i

5.

5

.

5

i.j

n

6

’

,

,

and P ⊆

X

. . .

X

: X

P

. Each finite frame can be represented

.

n

i

i

then as the ordered sum C

. . .

C

of its clusters.

.

n

f

6

6

?

g

.

.

We begin our study by developing a language of "canonical formulas" for

axiomatizing logics in NExt

and characterizing the constitution of their

Lin

frames. It will play the same role as the language of canonical formulas for

K,

F

. With every finite frame

⊆

W" R" R

⊆ C

. . .

C

and a cluster

5

.

n

.

.

.

assignment

⊆ (

"

) in it we associate the formula

t

t

t

.

,

h

i

—(

"

) ⊆ 9(

"

)

9(

"

)

9(

"

)

p

"

.

,

r

F

F

F

F

t

t

t

t

.

.

.

.

. -

where r is an arbitrary fixed point in

and

F

F

t

,

9(

"

) ⊆

p

p

: xRy "

(yRx)

x

y

.

f

.

-

g .

p

x

,

y

p

: xR

5

y "

(xRy)

,

.

f

.

-

g .

.

.

ADVANCED MODAL LOGIC

''

p

p

: x

⊆ y

x

y

p

x

,

y

p

:

(xRy)

,

f

. -

g .

f

. -

-

g .

.

.

p

x

.

y

.

i

i

p

:

i

n (

C

⊆

x" y

C

xRy)

t

m

,

f

.

1

7

.

?

.

g .

.

.

"

p

x

,

y

,

i

i

p

:

i

n (

C

⊆

x" y

C

xR5

y)

t

m

,

.

f

.

1

7

.

?

.

g .

p

: y

W

.

y

f

?

g

To explain the semantical meaning of these formulas. notice first that if

t

m

m

t

C ⊆ (

"

) for all clusters C then

⊆ —(

"

) iff

is reducible to

4 so

G

F

G

F

Lin

t

Lin

t

j

—(

"

) is a splitting of NExt

. Suppose now that

C ⊆

for some

i

F

'j

"

i

1" 3

and some cluster C in

. In this case

⊆ —(

"

) iff there exist

F

G

F

t

? f

g

'j

frames

. for 1

i

n. such that

⊆

. . .

and

⊆ —(C

"

C

)

i

n

i

i

i

.

G

G

G

G

G

t

.

.

.

for all 1

i

n. So it suffices to examine the situation when

⊆ —(C"

)

G

t

7

7

'j

for a cluster C . Assume for simplicity that

is a Kripke frame.

Case 8"

G

7

7

'j

t

j

j

t

t

m

j

C ⊆ (

"

). Then

⊆ —(C"

) iff

C

.

C ⊆ (

"

). Then C is

Case 0"

G

G

non-degenerate and

⊆ —(C"

) iff either

contains an R-final cluster of

G

G

t

'j

j

j 9 j

j

cardinality

C

or it has no R-final point at all.

C ⊆ (

"

). This

Case fl"

t

j

m

'j

is the mirror image of Case 3.

C ⊆ (

"

). If C is an irreflexive

Case ["

t

m

m

9 j

j

point then

is an irreflexive point as well whenever

⊆ —(C"

). If C is

G

G

t

non-degenerate and

⊆ —(C"

) then

satisfies the conditions of Cases 3

G

G

t

'j

and 2.

'j

EXAMPLE 3.36 Let — ⊆ —(

"

) where

a ⊆ (

"

) and

b ⊆ (

"

).

t

t

m

j

t

j

m

a

b

.

Then

⊆ — iff there exists a non-empty upward closed set X

P such

F

o o

that

x

X

y

X yRx. W

X

⊆

and

x

W

X

y

W

X xRy .

'j

?

)

?

1

?

[

fl

)

?

[

1

?

[

Hence

" 5" "

⊆ — (take X ⊆

y

:

3 5 y

) but

" 5" "

⊆ —.

Q

Q

R

p

since the real line contains no gaps.

h

i 'j

f

?

g

h

i j

THEOREM 3.38

.

There is an algorithm which. given a formula

. returns

formulas

such that

—(

"

)" . . . " —(

"

)

.

.

n

n

F

F

t

t

Lin

Lin

t

t

F

F

. ⊆

—(

"

)

. . .

—(

"

).

.

.

n

n

"

"

"

"

Proof

t

F

Let (

"

). 1

i

n. be the collection of all finite frames with type

i

i

assignments such that. for each i. (a) there is a countermodel

⊆

"

i

i

i

M

F

V

7

7

for . in which

is .-good for (

"

). (b) the depth of

does not exceed

i

i

i

i

V

F

F

t

h

i

5l(.) " 1. and (c) no cluster in

contains more than 3

points. where

i

F

v

5

1

9

v(.) is the number of variables in .

Let

refute —(

"

) under a valuation

. By the definition of (

"

).

i

i

i

i

F

G

U

t

F

t

the model

refutes . Define a valuation

in

by taking. for all variables

i

.

M

U

F

p in .

U

U

V

. (p) ⊆

(p

) : x

(p)

.

x

i

f

?

g

5

It is not hard to show by induction that

(:) ⊆

(p

) : x

(:)

.

x

i

U

U

V

for all :

. and so

refutes . under

. Thus

⊆ . implies

Sub

F

U

F

.

S

f

?

g

?

j

'
'
5[[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Ord

t

⊆ Log

[ " 5" "

: [ an ordinal

⊆

fh

i

g

Lin

j

m

—(

" (

" (

"

)))

"

[

o

E

Lin

t

⊆

⊆

.

,

,

,

"

] "

]

Lin

m

m

m

m

—(

" (

" (

"

)))

—((

" (

"

))"

)

"

[

5

"

5

[

O

n

⊆ Log

'n" 5" "

⊆

h

i

Ord

m

j

m

j

m

m

t

—((

" (

"

))

. . .

(

" (

"

)))

—(

" (

" (

"

)))

.

.

"

o

o

"

[

5

n

".

RD

G

⊆ Log

:

x(

xRx

y(xRy

z : xRzRy

⊆

))

⊆

?

"z

'

f

)

-

. 1

. f

g

fl

g

Lin

m

m

m

m

m

j

—(

" (

" (

"

)))

—(

" (

" (

"

))

(

" (

"

)))

.

"

[

5

"

[

5

o

LD

RD

⊆ the mirror image of

Z

t

⊆ Log

" 5" "

⊆

Z

h

i

RD

LD

j

j

j

m

—((

" (

"

))

(

" (

"

)))

.

"

"

o

o

"

—((

" (

"

))

(

" (

"

)))

m

j

j

j

.

Ds

Lin

n

⊆

p

p ⊆

.

.

o

o

n

".

n

.

.

"

.

Lin

m

m

m

m

—(

" (

" (

"

)

. . .

(

" (

"

))

"

)

.

.

"

[

5

5

[

n

".

Q

t

⊆ Log

" 5" "

⊆

Q

?

"z

'

h

i

Ds

E

.

t

"

R

t

⊆ Log

" 5" "

⊆

R

h

i

Q

m

j

j

m

t

—((

" (

"

))

(

" (

"

)))

.

"

o

o

Rd

t

⊆ Log

[ "

"

: [ an ordinal

⊆

fh

7

9i

g

Lin

j

m

,

—(

" (

" (

"

)))

"

[

#

Table 2. Axiomatizations of standard tense logics

F

F

t

⊆ —(

"

) for every i. The converse direction is rather technical4 we

i

i

j

refer the reader to [Wolter 1996d].

.

"Canonical" axiomatizations of some standard linear tense logics are

shown in Table 2. where we use the following abbreviations. Given a ,-

nite frame

⊆ C

. . .

C

. we write —((C

"

C

)

. . .

(C

"

C

))

.

.

.

n

n

n

F

t

t

.

.

.

.

instead of —(

"

) and —(

" (C

"

C

)

. . .

(C

"

C

)) instead of

.

.

n

n

F

t

t

t

.

.

[

—((C

"

C

)

. . .

(C

"

C

))

—((

" (

"

))

(C

"

C

)

. . .

(C

"

C

)).

.

.

.

.

n

n

n

n

t

t

j

j

t

t

.

.

.

.

.

"

o

—((C

"

C

)

. . .

(C

"

C

)"

) is defined analogously.

t

t

.

.

n

n

.

.

Now we exploit the formulas —(

"

) to characterize the

-irreducible

[

F

t

T

ADVANCED MODAL LOGIC

5[5

logics in NExt

. Recall that every logic L

NExtL

is represented as

Lin

.

?

L ⊆

L.

L : L. is

-irreducible

.

f

(

g

,

,

So such a characterization can open the door to a better understanding of

the structure of the lattice NExt

. The

-irreducible logics will be de-

Lin

scribed semantically as the logics determined by certain descriptive frames.

T

DEFINITION 3.36 (1) Denote by

the non-degenerate cluster with k " 0

k

points.

.

#

(3) Let '

(0) be the strictly ascending chain

' " 5" "

of natural num-

bers. '

(1) the chain

' "

"

. '

(3) the ascending chain of natural num-

.

.

h

i

bers in which precisely the even points are reflexive. '

(2) the chain in

h

7

9i

.

which precisely the multiples of 2 are reflexive. and so on4 '

(n) is the

.

mirror image of '

(n).

.

(2)

(0"

) is the mirror image of the frame introduced in Example 3.32.

C

.

C

.

.

.

#

.

i.e.

(0"

) ⊆

'

(0)

" P

. where P consists of all cofinite sets contain-

ing

and their complements. We generalize this construction to chains

.

#

h

#

i

.

#

'

(n) and clusters

. Namely. for n 5 ' . k " 1 and

⊆

a

" . . . " a

.

.

.

k

k

k

#

#

f

g

5

we put

C

k

k

(n"

) ⊆

'

(n)

" P

"

.

.

#

h

#

i

where P is the set of possible values generated by

X

: 0

i

k

1

. for

i

X

⊆

a

kj " i : j

'

. 0

i

k

1.

(

" n) denotes the mirror

i

i

C

k

f

7

7

[

g

f

g 6 f

?

g

7

7

[

#

image of

(n"

).

C

k

C

.

.

.

.

#

.

.

(5)

(0"

" 0) ⊆

'

(0)

'

(0)" P

. where P consists of all cofinite

sets containing

and their complements.

.

#

h

#

i

#

It is easy to check that the frames defined in (2) and (5) are descriptive

and a singleton

x

is in P iff x

.

k

f

g

'? #

For a class of frames

. we denote by

the class of finite sequences of

.

frames from

and let [

] ⊆

[

] :

. The class of finite clusters

.

.

F

F

C

C

and the frames of the form (2) in Definition 3.36 is denoted by

4 put also

C

C

f

? C

g

.

B

⊆

(0"

" 0)

.

.

C

.

B

f

#

g 6 B

THEOREM 3.39

L

NExt

Each logic

is determined by a set

Lin

[

]

:

.

If

is .nitely axiomatizable then

for some set

L

L ⊆ Log

[

]

:

.

.

C

C ff

B

?

C ff

B

Proof

We explain the idea of the proof of the first claim. Suppose that

M

F

V

t

t

.

.

⊆

"

is a countermodel for — ⊆ —((C

"

C

)

. . .

(C

"

C

)) based

.

.

n

n

h

i

.

on a descriptive frame

⊆

W" R" R

" P

. We must show that there exists

5

F

G

G

F

[

] refuting — and such that Log

Log

. Consider the sets

.

h

i

?

B

(

W

⊆

y

W : (

" y)

⊆

p

: x

C

.

i

x

i

M

f

?

j

f

?

gg

"

5[ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

One can easily show that W

are intervals in

and

⊆

. . .

. for

i

n

.

F

F

F

F

.

.

the subframes

of

induced by W

. Moreover.

⊆ [

] is as required

i

i

F

F

G

G

if

⊆

" . . . "

is a sequence in

such that Log

Log

. and

n

.

i

i

.

G

G

G

G

F

G

G

t

i

i

i

i

⊆ —(C

"

C

). for 1

i

n. Frames

with those properties are

h

i

B

(

'j

7

7

constructed in [Wolter96d].

.

EXAMPLE 3.20 The logic

is determined by the frames

[

] which

t

.

Q

F

contain no pair of adjacent irreflexive points. and

is determined by the

t

R

?

B

frames

[

] which contain neither a pair of adjacent irreflexive points

.

F

nor a pair of adjacent non-degenerate clusters.

?

B

It is not difficult to show now that the logics Log

. for

[

]. coincide

.

F

F

with the

-irreducible logics in NExt

. Our first aim is achieved. and

Lin

?

B

in the remaining part of this section we shall draw consequences of this

T

result. Using the same sort of arguments as in the proof of Theorem 3.31

and Kruskal's [1960] Tree Theorem one can prove

COROLLARY 3.21 (i)

NExt

Al l .nitely axiomatizable logics in

are de5

Lin

cidable:

(ii)

A logic

is .nitely axiomatizable whenever there exists

such

L

n 5 '

that

L

NExt

Ds

n

:

?

It follows in particular that all logics in NExt

and all logics of reflexive

t

Q

frames are finitely axiomatizable and decidable.

Now we formulate two corollaries concerning the Kripke completeness of

linear tense logics. First. it is not hard to see that every logic in NExt

Lin

characterized by an infinite frame in [

] is Kripke incomplete. Using this

observation one can prove

.

B

COROLLARY 3.23

L

NExt

Suppose

and there is a Kripke frame of

Lin

in.nite depth for

: Then there exists a Kripke incomplete logic in

L

NExtL

:

?

This result means in particular that in Tense Logic we do not have ana-

logues of the unimodal completeness results of Bull [1966b] and Fine [1985c].

However. if a logic is complete then it is determined by a simple class of

frames. Let

be the class frames containing finite clusters and frames of

the form (3) in Definition 3.36.

K

THEOREM 3.22

NExt

Each Kripke complete logic in

is determined by

Lin

a subset of

[

]

:

.

K

One of the main types of logics considered in conventional Tense Logic

are logics determined by strict linear orders. known also as

. We

timeffilines

call them

. All logics in Table 2. save

. are t-line logics.

tffiline logics

Rd

t

ADVANCED MODAL LOGIC

5[—

T-line logics were defined semantically. and now we are going to determine

a necessary syntactic condition for a linear tense logic to be a t-line logic.

Given a frame

. we denote by

the frame that results from

by

-

F

F

F

replacing its proper clusters with reflexive points. Call L

NExt

a

Lin

tffiaxiom logic

if L is axiomatizable by a set of formulas of the form —(

"

)

?

F

t

in which

contains no proper clusters.

F

PROPOSITION 3.25

The fol lowing conditions are equivalent for al l logics

L

NExt

Lin

"

?

(i) L

is a tffiaxiom logic'

(ii)

⊆ L

⊆ L

implies

. for every

-

[

]

:

.

F

F

F

(iii) —(

"

)

L

—(

"

)

implies

L

.

for every .nite

:

G

t

G

t

G

-

j

j

?

B

."

?

?

Proof

The implications (i)

(ii) and (iii)

(i) are clear. To prove that

(ii)

(iii). suppose —(

"

)

L. Then there exists a frame

[

] for L

-

.

G

t

F

8

8

8

'?

?

B

refuting —(

"

). Without loss of generality we may assume that

contains

-

G

t

F

no proper clusters. By enlarging some clusters in

we can construct a frame

F

H

H

F

H

G

H

t

[

] such that

⊆

and

⊆ —(

"

). In view of (ii).

⊆ L and so

.

-

?

B

'j

j

.

—(

"

)

L.

G

t

'?

It follows that the t-axiom logics form a complete sublattice of the lattice

NExt

.

Lin

THEOREM 3.27 (i)

Al l .nitely axiomatizable tffiaxiom logics are Kripke

complete:

(ii)

Al l tffiline logics are tffiaxiom logics:

Proof

Lin

t

G

(i) Suppose that L ⊆

—(

"

) : i

I

. for some finite set

-

i

i

I . By Theorem 3.39. L is determined by a subset of [

]. For

[

].

F

" f

?

g

.

.

.

.

B

?

B

let k

be the Kripke frame that results from

by replacing all

(n"

)

F

F

C

k

and

(

" n) with '

(n) and '

(n). respectively. Then we clearly have

C

k

.

.

#

Logk

Log

. and

⊆ —(

"

) iff k

⊆ —(

"

). It follows that L is

-

-

F

F

F

G

F

G

t

t

#

Kripke complete. (ii) Suppose that L is a t-line logic. By Proposition 3.25

ff

j

j

(2). it suffices to observe that

⊆ —(

"

) iff

⊆ —(

"

). for all time-lines

-

F

G

F

G

t

t

F

G

and all finite

.

.

j

j

So the fact that in Table 2 all t-line logics are axiomatized by canon-

ical formulas of the form —(

"

) is no accident. Finding and verifying

-

G

t

axiomatizations of t-line logics becomes almost trivial now.

EXAMPLE 3.26 Let us check the axiomatization of

in Table 2. Put

t

Z

L ⊆

—((

" (

"

))

(

" (

"

)))

—((

" (

"

))

(

" (

"

))).

RD

LD

j

j

j

m

m

j

j

j

.

.

."

t

t

We assume that

5

whenever

replaces

in

8

C

"

"

C

G

"

"

o

o

"

o

o

5[(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

By Theorem 3.27. L is complete. By Theorem 3.22. L is then determined by

a subset of [

]. Clearly this set contains

" 5" "

. possibly

for k " 0.

.

Z

k

and nothing else. But the logic of

contains

. for all k " 0.

t

k

Z

K

h

i

#

#

We conclude this section by discussing the decidability of properties of

logics in NExt

. In Section 5.5 it will be shown that almost all interesting

Lin

properties of calculi are undecidable in NExt

and even in NExt

. In

K

S,

NExt

the situation is different. as was proved in [Wolter 1996d. 1998d].

Lin

THEOREM 3.28 (i)

.

There are algorithms which. given a formula

. decide

whether

.

Lin

has FMP. interpolation. whether it is Kripke complete.

strongly complete. canonical.

5persistent:

"

R

(ii)

A linear tense logic is canonical i, it is

5persistent i, it is complete

and its frames are .rst order de.nable:

D

(iii)

NExt

If a logic in

has a frame of in.nite depth then it does not

Lin

have interpolation:

So NExt

provides an interesting example of a rather complex lattice

Lin

of modal logics for which almost all important properties of calculi are

decidable. We shall not go into details of the proof here but discuss quite

natural criteria for canonicity and strong completeness of logics in NExt

Lin

required to prove this theorem. Denote by

the class of frames containing

"

B

together with frames

(n

"

" n

) defined as follows. Suppose k " 1.

.

,

C

k

B

#

n

" n

5 ' are such that n

" n

" 0 and

⊆

a

" . . . " a

. Then

.

,

.

,

.

.

k

k

#

f

g

5

C

k

k

(n

"

" n

) ⊆

'

(n

)

'

(n

)" P

"

.

,

.

,

.

.

.

.

#

h

#

i

where P is the set of possible values generated by

X

: 0

i

k

1

. for

i

f

7

7

[

g

X

⊆

a

kj " i : j

'

k. j . " i. : j

'

i

i

f

g 6 f

?

g 6 f

?

g

and

0

" 1

" . . . " n

" . . .

being the points in '

(n

).

.

.

.

,

.

f

g

Let

be the class of frames of the form

F

0" . . . " n

" 5" "

0" . . . " n

" 5" "

or

0" . . . " n

" 5" "

.

.

,

.

.

.

hf

g

i

#

hf

g

i

hf

g

i

THEOREM 3.26 (i)

L

NExt

A logic

is canonical i, the underlying

Lin

Kripke frame of each frame

for

validates

as wel l:

[

]

L

L

?

F

.

"

?

B

(ii)

L

NExt

A logic

is strongly complete i, for each frame

[

]

Lin

F

.

"

validating

. there exists a Kripke frame

L

for

which results from

by

L

G

F

?

?

B

replacing

every

with

or

(n"

)

'

(n)

'

(n)

. for some

. and

C

k

H

k

H

.

.

.

.

5

#

#

? F

every

with

or

(

" n)

'

(n)

'

(n)

. for some

. and

C

k

k

H

H

.

.

.

.

5

#

#

? F

ADVANCED MODAL LOGIC

5[)

every

with

. for some

:

(n

"

" n

)

'

(n

)

'

(n

)

C

k

H

H

.

,

.

,

.

.

.

.

5

#

? F

EXAMPLE 3.29 The logic

is not canonical because

(3"

)

⊆

but

t

t

R

R

C

,

.

.

,

R

R

F

R

'

(3)

⊆

. However.

is strongly complete. since

⊆

whenever

t

t

t

#

j

G

F

G

R

[

] validates

and

is obtained from

as in the formulation of

.

t

"

#

'j

j

?

B

Theorem 3.26 with

⊆

.

H

5 ? F

One can also use Theorem 3.26 to construct two strongly complete logics

L

" L

NExt

whose sum L

L

is not strongly complete (see [Wolter

Lin

.

,

.

,

1996c]).

?

"

.,' Bimodal provability logics

Bimodal provability logics emerge when combinations of two different prov-

ability predicates are investigated. for example. if

is understood as "it

.

.

is provable in PA" and

as "it is provable in ZF". In contrast to the

,

.

situation in unimodal provability logic. where almost all provability pred-

icates behave like the necessity operator

in

. there exist quite a lot

.

GL

of different types of bimodal provability logics. Various completeness re-

sults extending Solovay's completeness theorem for

to the bimodal case

GL

were established by Smoryonski [1967]. Montagna [1968]. Beklemishev [1995.

1996] and Visser [1997]. Here we will not deal with the interpretation of

modal operators as provability predicates but sketch some results on modal

logics containing the bimodal provability logic

CSM

GL

GL

⊆ (

)

p

p

p

p

.

.

,

,

.

,

.

.

.

.

.

&

"

.

"

.

(named so by Visser [1997] after Carlson. Smoryonski and Montagna). A

number of provability logics is included in this class. witness the list below.

(As in unimodal provability logic we have quasi-normal logics among them.

i.e. sets of formulas containing

and closed under modus ponens and

K

,

substitutions (but not necessarily under .,

.). Recall that we denote by

i

.

L " Φ the smallest quasi-normal logic containing L and Φ.)

CSM

CSM

PRL

.

.

,

.

ZF

⊆

(

p

p). (This is

in [Smoryonski

.

.

5

"

.

1967] and

in [Montagna 1968].)

F

NB

CSM

⊆

(

p

p)

(

q

q).

.

.

.

,

,

.

.

.

.

.

5

"

-

.

.

.

CSM

CSM

PRL

⊆

"

p

p.

(This is

" Reflection

in

,

.

.

ZF

.

.

.

5

.

[Smoryonski 1967] and

in [Montagna 1968].)

F

.

CSM

CSM

PRL

⊆

"

p

p.

(This is

" Reflection

in

:

,

,

ZF

:

.

.

5

.

[Smoryonski 1967].)

5[0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

NB

NB

⊆

"

p

p "

p

p.

,

.

,

,

.

.

.

.

5

.

.

A remarkable feature of

is that—like in

—we have uniquely de-

CSM

GL

.

termined definable fixed points.

THEOREM 3.50 (Smoryonski 1967)

.(p)

Let

be a formula in which every

occurrence of

lies within the scope of some

or some

: Then

p

.

,

.

.

(i)

:

there exists a formula

containing only the propositional variables of

.(p)

p

:

.(:)

difierent from

such that

CSM

'

.

(ii)

((p

.(p))

(q

.(q)))

(p

q)

.

CSM

:

.

.

5

?

5

.

5

.

5

?

In the remaining part of this section we are concerned with subframe

logics containing

. the main result stating that those of them that

CSM

.

are finitely axiomatizable are decidable. All the provability logics introduced

above turn out to be subframe logics. so we obtain a uniform proof of their

decidability. An interesting trait of subframe logics in Ext

is that

CSM

.

(as a rule) they are Kripke incomplete4 in the list above such are

CSM

i

.

i ⊆ 1" 3" 2. and

. i ⊆ 1" 3. The proof extends the techniques introduced

i

NB

by Visser [1997]4 for details we refer the reader to [Wolter 1998a].

First we develop—as was done for NExt

and NExt

—a frame the-

K,

Lin

oretic language for axiomatizing subframe logics in the lattice Ext

.

CSM

.

A finite frame

⊆

W" R

" R

validates

iff both R

and R

are

.

,

.

.

,

G

CSM

transitive. irreflexive. R

R

and

,

.

h

i

ff

x" y " z (xR

y

yR

z

xR

z ).

.

,

,

)

.

.

In this section all (not only finite) frames are assumed to satisfy these con-

ditions.

save irre—exivity

.

A finite frame

is called a

if it has precisely one root

surrogate frame

F

r and all points different from r are R

-irreflexive. Surrogate frames will

,

provide the language to axiomatize subframe logics in Ext

. A

CSM

normal

.

surrogate frame

W" R

" R

is a surrogate frame in which the root r is

.

,

R

-irreflexive. We write xR

y iff xR

y and

yR

x. Given a frame

⊆

.

i

i

G

i

h

i

p

V " S

" S

" Q

for

and a surrogate frame

⊆

W" R

" R

. a map h

CSM

.

,

.

.

,

-

F

h

i

h

i

from V onto W is called a

of

to

if for i

1" 3

and all

weak reduction

G

F

x" y

V .

? f

g

?

5

xS

y implies f (x)R

f (y).

i

i

p

f (x)R

f (y) implies

z

V (xS

z

f (z ) ⊆ f (y)).

i

i

5

1

?

.

.

f

(X )

Q for all X

W .

5

5

?

ff

(The standard definition of reduction is relaxed here in the second condi-

tion.) Each weak reduction to a

-frames is a usual reduction. since in

CSM

.

ADVANCED MODAL LOGIC

5[?

this case R

⊆ R

. A frame

is said to be

to a surro-

weakly subreducible

G

i

i

p

gate frame

if a subframe of

is weakly reducible to

. To describe weak

F

G

F

subreducibility syntactically. with each surrogate frame

⊆

W" R

" R

we

.

,

F

associate the formula

h

i

F

F

F

.

—(

) ⊆ 9(

)

9(

)

p

"

.

r

.

. -

where r is the root of

and

F

F

,

9(

) ⊆

p

p

: xR

y " x" y

W

x

y

.

.

p

f

.

?

g .

.

.

,

p

p

x

,

y

p

: xR

y " x" y

W

,

f

.

?

g .

p

p

: x

⊆ y " x" y

W

x

y

f

. -

?

g .

.

p

x

.

.

y

p

:

(xR

y)" x" y

W

,

f

. -

-

?

g .

.

p

x

,

,

y

p

:

(xR

y)" x" y

W

.

,

f

. -

-

?

g

.

LEMMA 3.51

⊆

For every surrogate frame

and every

5frame

.

F

G

G

CSM

.

—(

)

i,

is weakly subreducible to

:

F

G

F

'j

It follows immediately that

—(

) and

"—(

) are subframe

.

.

CSM

CSM

F

F

logics. Conversely. we have the following completeness result.

"

THEOREM 3.53 (i)

.

There is an algorithm which. given a formula

such

that

is a subframe logic. returns surrogate frames

for

CSM

F

F

.

" .

.

" . . . "

n

which

CSM

CSM

F

F

.

.

.

" . ⊆

" —(

) " . . . " —(

).

n

(ii)

.

.

There is an algorithm which. given a formula

such that

CSM

.

"

is a subframe logic. returns normal surrogate frames

such that

.

" . . . "

n

F

F

CSM

CSM

F

F

.

.

.

. ⊆

—(

)

. . .

—(

).

n

"

"

"

"

Table 5 shows axiomatizations of the logics introduced above by means of

formulas of the form —(

). In this section we adopt the convention that in

F

figures we place the number 1 nearby an arrow from x to y if xR

y and

.

xR

y . An arrow without a number means that xR

y (and therefore xR

y

,

,

.

-

as well).

The proof of decidability is based on the completeness of subframe logics

in Ext

with respect to rather simple descriptive frames. With every

CSM

.

surrogate frame

we associate a finite set of frames E(

) ⊆

: A

F

F

F

A

f

?

Seq

. Loosely. it is defined as follows. Let us first assume that the root r

F

g

of

is R

-irreflexive. Then the frames in E(

) are the results of inserting an

,

F

F

infinite strictly descending R

-chain. denoted by C ('). between each non-

.

degenerate R

-cluster C and its R

-successors. This defines R

uniquely.

.

.

.

'
5[fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

CSM

CSM

⊆

—(

)

.

.

5

"

CSM

CSM

"

p

p

⊆

" —(

)

.

.

.

.

"

5

.

5

CSM

CSM

"

p

p

⊆

" —(

)

.

,

.

.

.

.

o

CSM

CSM

"

p

p ⊆

" —(

)

.

,

.

.

.

.

.

o

.

o

.

"

NB

CSM

⊆

—(

)

—(

)

.

.

.

.

5

5

5

5

'I

"(

'I

"(

.

.

'

"

'

"

"

5

"

5

"

.

.

.

5

5

5

5

'I

"(

'I

"(

.

.

'

"

'

"

—(

)

—(

)

5

"

5

Table 5. Axiomatizations of provability logics

However. R

may be defined in different ways. since a point R

-seeing a

,

,

point in C need not (but may) R

-see certain points in the chain C (').

,

F

To be more precise. the set Seq

consists of all sequences A of the form

A ⊆

A

: xR

x" x

W

.

x

.

h

?

i

where A

is a subset of

y

W

C : yR

x

such that for all y and z .

x

,

y

A

and zR

y imply z

A

. For each non-degenerate R

-cluster C .

x

x

.

.

f

?

[

g

?

?

denote by C (') the set

(n" C ) : n

'

. Finally. given A

Seq

. we

F

construct

⊆

V " S

" S

as the frame satisfying the following conditions:

F

f

?

g

?

A

.

.

h

i

V ⊆ W

C (') : C a non-degenerate R

-cluster in

4

.

F

5

6

f

g

S

R

⊆ S

(W

W ). for i

1" 3

4

i

i

5

0

’

? f

g

S

is defined so that C (') becomes an infinite descending chain be-

.

5

tween C and its immediate successors4

for every non-degenerate R

-cluster C .

.

5

"

((C (')

C )

(C (')

C ))

S

⊆

.

,

6

’

6

0

fl

for all y

W

C and x

C ('). xS

y iff CR

y .

,

,

?

[

?

"

"

for all y

W

C . C ⊆

j : 0

j

m

1

and x

C ('). yS

x

,

iff

i

'

j

m

1 (x ⊆ (im " j" C )

y

A

).

j

?

[

f

7

7

[

g

?

1

?

1

7

[

.

?

"

for all x

C (') and y

V

C . xS

y iff C S

y .

,

,

?

?

[

We illustrate this technical definition by a simple example.

ADVANCED MODAL LOGIC

5['

.

5

5

"

"

0

5

5

"

"

.

5

5

"

"

0

.
5

5

.

.

.

.

.

c

d

1

1

1

.0

.0

.0

o

o

o

o

o

o

" "

" "

" "

5

5

5

5

5

5

a

b

(a)

(b)

(c)

Figure 13.

EXAMPLE 3.52 Construct E(

) for the frame

in Fig. 13 (a).

In this

F

F

case we have two R

-reflexive points. namely c and d. So. Seq

consists of

.

F

pairs

A

" A

. There are four different pairs and so we have four frames

c

d

h

i

in E(

): the frame in Fig. 13 (b) is

and that in (c) is

.

:

a

:

b

F

F

F

h—

—i

hf

g

f

gi

F

F

:

b

a

:

b

,

is obtained from

by omitting the R

-arrows starting from

h—

f

gi

hf

g

f

gi

a. save the arrow to c. and

is obtained from

by omitting

a

:

a

:

b

F

F

the R

-arrows starting from b. save the arrow to d.

,

hf

g

—i

hf

g

f

gi

Suppose now that the root r of

⊆

W" R

" R

is R

-reflexive. We define

.

,

,

F

F

A

as in the previous case. but this time we also insert an infinite strictly

h

i

descending R

-chain C (') between r and its R

-successors.

,

.

We have defined the relational component of our frames and now turn to

their sets of possible values. Given

⊆

V " S

" S

and a non-degenerate

F

A

.

,

h

i

R

-cluster C ⊆

j : 0

j

m

1

in

. let

.

F

f

7

7

[

g

P

⊆

j

(im " j" C ) : i

'

: j ⊆ 0" . . . " m

1

C

ff

g 6 f

?

g

[

g

and denote by P the closure of

x

: x

V "

xS

x

P

: C is a non-degenerate R

-cluster in

.

.

C

F

ff

g

?

-

g 6 f

g

under intersections and complements in V . The resultant general frame is

denoted by

(

) ⊆

V " S

" S

" P

. One can check that it is a descriptive

G

F

A

.

,

h

i

frame for

. The following completeness result is proved similarly to

CSM

.

that in Section 3.5.

THEOREM 3.55 (i)

NExt

Each subframe logic in

is determined by

CSM

.

a set of frames of the form

(

)

. in which

is a normal surrogate frame

G

F

F

A

and

:

A

Seq

F

?

55[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

(ii)

Ext

Each subframe logic in

is determined by a set of frames

CSM

.

with distinguished worlds of the form

(

)" r

in which

is a surrogate

G

F

F

A

frame with root

and

r

A

Seq

F

:

.

:

?

As a consequence of Theorem 3.55 and the fact that. for each surrogate

frame

with root r and each A

Seq

. both the logics of

(

) and

F

F

G

F

A

G

F

(

)" r

are decidable. we obtain

A

?

.

:

THEOREM 3.57

Al l .nitely axiomatizable subframe logics in

Ext

CSM

.

are decidable:

We conjecture that the method above can be extended to logics without

the

-axioms. i.e. all finitely axiomatizable subframe logics containing

GL

(

)

p

p

p

p are decidable.

K,

K,

.

,

,

.

,

.

.

.

.

.

&

"

.

"

.

2 SUPERINTUITIONISTIC LOGICS

Although C.I. Lewis constructed his first modal calculus

in 1916. it

S5

was G;odel's [1922] two page note that attracted serious attention of math-

ematical logicians to modal systems. While Lewis [1916] used an abstract

necessity operator to avoid paradoxes of material implication. G;odel [1922]

and earlier Orlov [1936]

treated

as "it is provable" to give a classical in-

.8

.

terpretation of intuitionistic propositional logic

by means of embedding

Int

it into a modal "provability" system which turned out to be equivalent to

Lewis'

.

S,

Approximately at the same time G;odel [1923] observed that there are

infinitely many logics located between

and classical logic

. which—

Int

Cl

together with the creation of constructive (proper) extensions of

by

Int

Kleene [1957] and Rose [1972] (realizability logic). Medvedev [1963] (logic

of finite problems). Kreisel and Putnam [1978]—gave an impetus to study-

ing the class of logics intermediate between

and

. started by Umezawa

Int

Cl

[1977. 1979]. G;odel's embedding of

into

. presented in an algebraic

Int

S,

form by McKinsey and Tarski [1956] and extended to all intermediate logics

by Dummett and Lemmon [1979]. made it possible to develop the theories

of modal and intermediate logics in parallel ways. And the structural results

of Blok [1986] and Esakia [1989a.b]. establishing an isomorphism between

the lattices Ext

and NExt

. along with preservation results of Mak-

Int

Grz

simova and Rybakov [1985] and Zakharyaschev [1991]. transferring various

properties from modal to intermediate logics and back. showed that in many

respects the theory of intermediate logics is reducible to the theory of logics

in NExt

.

S,

.5

Orlov6s paper remained unnoticed till the end of the 5'fl[s8 It is remarkable also for

constructing the :rst system of relevant logic8

ADVANCED MODAL LOGIC

555

For

Int

⊆

" p

Cl

Int

⊆

" p

p

, -

SmL

Int

⊆

" (

q

p)

(((p

q)

p)

p)

-

.

.

.

.

.

KC

Int

⊆

"

p

p

-

, --

LC

Int

⊆

" (p

q)

(q

p)

.

,

.

SL

Int

⊆

" ((

p

p)

p

p)

p

p

--

.

. -

,

. -

, --

KP

Int

⊆

" (

p

q

r)

(

p

q)

(

p

r)

-

.

,

.

-

.

,

-

.

BD

Int

bd

n

n

⊆

"

. where

bd

bd

bd

.

.

.

".

".

".

⊆ p

p

"

⊆ p

(p

n

n

n

n

)

, -

,

.

n

BW

Int

n

i

⊆

"

(p

p

)

j

i

5.

j

i

5

.

n

BTW

Int

n

i

j

i

⊆

"

(

p

p

)

(

p

p

)

j

W

W

.

i.j

n

i

5.

j

i

5

T

Int

n

i

⊆

"

((p

p

)

j

p

)

j

p

i

V

W

W

i

5.

i

j

5

i

j

5

i

5.

,

,

-

-

. -

.

-

.

-

n

n

B

Int

n

i

⊆

"

(

p

p

)

j

p

i

V

W

W

W

i

5.

i

j

5

i

5.

-

5

.

n

n

.

.

.

NL

Int

nf

n

⊆

"

. where

n

V

W

W

nf

nf

nf

nf

⊆

.

⊆ p.

⊆

p.

⊆

.

.

,

,

:

-

]

nf

nf

nf

⊆

.

,

":

,

".

,

",

m

m

m

nf

nf

nf

⊆

,

"'

,

":

,

".

m

m

m

,

.

Table 7. A list of standard superintuitionistic logics

To demonstrate this as well as some features of intermediate logics is

the main aim of this part. We will use the same system of notations as

in the modal case. In particular. Ext

is the lattice of all logics of the

Int

form

" Φ (where Φ is an arbitrary set of formulas in the language of

Int

Int

and " as before means taking the closure under modus ponens and

substitution)4 we call them

or

for short.

superintuitionistic logics

siffilogics

Basic facts about the syntax and semantics of

and relevant references

Int

can be found in

. A list of some "standard" si-logics is

Intuitionistic Logic

given in Table 7.

:,. Intuitionistic frames

As in the case of modal logics. the adequate relational semantics for si-logics

can be constructed on the base of the Stone representation of the algebraic

"models" for

. known as

(or

)

. It is hard

Heyting

pseudo5Boolean

algebras

Int

to trace now who was the first to introduce intuitionistic general frames—the

earliest references we know are [Esakia 1985] and [Rautenberg 1989]—but in

any case. having at hand [Joonsson and Tarski 1971] and [Goldblatt 1986a].

the construction must have been clear.

"
"
"
"
"
55ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

An

(

)

is a triple

⊆

W" R" P

in which R is a

intuitionistic

general

frame

F

partial order on W

⊆

and P . the

in

. is a collection

set of possible values

h

i

F

of upward closed subsets (cones) in W containing

and closed under the

fl

Boolean

.

. and the operation

(for

) defined by

fl

0

6

(

.

X

Y ⊆

x

W :

y

x

(y

X

y

Y )

.

(

f

?

)

?

3

?

.

?

g

If P contains all upward closed subsets in W then we call

a

Kripke frame

F

and denote it by

⊆

W" R

. An important feature of intuitionistic models

F

M

F

V

V

F

⊆

"

(

. a

in

. maps propositional variables to sets in P )

valuation

h

i

is that

(.). the

of a formula . is always upward closed.

truthffivalue

h

i

V

Every intuitionistic frame

⊆

W" R" P

gives rise to the Heyting algebra

F

"

h

i

F

F

⊆

P"

"

"

"

called the

of

. Conversely. given a Heyting algebra

dual

h

0

6

(

fli

A

A

⊆

A"

"

"

"

. we construct its relational representation

⊆

W" R

"

h

.

,

.

:i

h

i

by taking W to be the set of all prime filters in

(a filter

is

if it

prime

A

is proper and a

b

implies a

or b

). R to be the set-theoretic

r

inclusion

and

ff

,

? r

? r

? r

P ⊆

W : a

: a

A

.

ffr ?

? rg

?

g

It is readily checked that

. the

of

. is an intuitionistic frame.

dual

"

A

A

A

A

A

⊆

"

"

(

)

and

is differentiated.

in the sense that

tight

"

2

xRy iff

X

P (x

X

y

X )"

)

?

?

.

?

and

. i.e. for any families

P and

W

X : X

P

.

compact

X ff

Y ff f

[

?

g

(

) ⊆

x

W :

X

Y

(x

X

x

Y )

⊆

X 6 Y

f

?

)

? X )

? Y

?

.

?

g '

fl

,

whenever

(

)

⊆

for every finite subfamilies

.

.

.

.

.

.

Frames with these three properties (actually differentiatedness follows from

T

X

6 Y

fl

X

ff X

Y

ff Y

tightness) are called

.

In the same way as in the modal case

descriptive

one can prove that

is descriptive iff

(

)

. Duality between the

F

F

F

"

⊆

"

2

basic truth-preserving operations on algebras and descriptive frames (the

definitions of generated subframes. reductions and disjoint unions do not

change) is also established by the same technique.

Since every consistent si-logic L is characterized by its Tarski!Lindenba-

um algebra

. we conclude that L is characterized also by a class of intu-

L

A

itionistic frames. say by the dual of

.

L

A

Refined finitely generated frames for

look similarly to those for

:

Int

K,

the only difference is that now all clusters are simple and the truth-sets must

be upward closed. Fig. 12 showing (a) the free 1-generated Heyting algebra

AInt

FInt

(1) and (b) its dual

(1) will help the reader to restore the details.

AInt

(1) was first constructed by Rieger [1959] and Nishimura [1960]4 it is

called the

Rieger9Nishimura lattice

. The formulas

defined in Table 7

nf

n

'
'
ADVANCED MODAL LOGIC

55—

o

]

. . .

6

6

6

6

6

6

nf

.

6

6

6

—

nf

o

'I

"(

'I

o

p

3

1

16

o

'I

o

"

"

1

'

"

'

1

'

1

'

"

'

1

nf

ff

nf

-

5

2

'

16

1

"(

'I

o

"(

o

o

'I

o

"

"

"

'

"

1

'

'

1

"

'

"

1

'

nf

8

nf

"

6

'

7

16

1

o

'I

"(

'I

o

o

'I

o

"

"

'

"

'

1

'

'

"

'

1

'

nf

:

nf

'

"(

'I

o

"(

o

6

8

'

16

o

o

"

'I

"

1

"

'

"

1

'

'

1

'

1

"

'

"

1

'

nf

nf

,

.

10

9

'

o

'I

"(

o

o

o

'

"

'

"

.

AInt

F

(1)

Int

?

(1)

6 6 6 6 6 6

6 6 6 6 6 6

o

:

(a)

(b)

Figure 12.

and used for the construction are known as

(see also

Nishimura formulas

Section 2 of

).

Intuitionistic Logic

At the algebraic level the connection between

and

discovered by

Int

S,

G;odel is reflected by the fact. established in [Mckinsey and Tarski 1956].

that the algebra of open elements (i.e. elements a such that

a ⊆ a) of

.

every modal algebra for

(known as a

4 see

topological Boolean algebra

S,

[Rasiowa and Sikorski 1962]) is a Heyting algebra and conversely. every

Heyting algebra is isomorphic to the algebra of open elements of a suitable

algebra for

. We explain this result in the frame-theoretic language.

S,

Given a frame

⊆

W" R" P

for

(which means that R is a quasi-

F

S,

order on W ). we denote by

W the set of clusters in

—more generally.

,

F

h

i

,

,

X ⊆

C (x) : x

X

—and put C (x)

C (y) iff xRy .

f

?

g

,

,

,

P ⊆

X : X

P

X ⊆

X

⊆

X : X

P

X ⊆ X

.

.

f

?

.

g

f

?

.

3g

It is readily checked that the structure

⊆

W"

R"

P

is an intuition-

,

,

,

,

F

istic frame (for instance.

(X )

(Y ) ⊆

(

(

X

Y )))4 we call it the

,

,

,

h

i

.

skeleton

skeleton

of

. The

of a model

⊆

"

for

is the intuitionistic

F

M

F

V

S,

(

[

6

model

⊆

"

. where

(p) ⊆

(

p).

,

,

,

,

M

F

V

V

V

h

i

.

Denote by T the

prefixing

to all subformulas of a

G-odel translation

h

i

.

given intuitionistic formula.

By induction on the construction of . one

.ff

.'

.

The translation de:ned in "Gfiodel 5'——" does not pre:x

to conjunctions and dis2

55(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

can easily prove the following

LEMMA 2.1 (Skeleton)

For every model

for

. every intuitionistic for5

M

S,

mula

and every point

in

.

.

x

M

,

M

M

(

" C (x))

⊆ .

(

" x)

⊆ T (.).

i,

j

j

It follows that .

implies T (.)

. To prove the converse we

Int

S,

should be able to convert intuitionistic frames

into modal ones with the

F

?

?

skeleton (isomorphic to)

. This is trivial if

is a Kripke frame—we can

F

F

just regard it to be a frame for

. which in view of the Kripke completeness

S,

of both

and

. shows that T really embeds the former into the latter.

Int

S,

i.e.

.

iff T (.)

.

Int

S,

?

?

In general. the most obvious way of constructing a modal frame from an

intuitionistic frame

⊆

W" R" P

is to take the closure

P of P under the

F

.

Boolean operations

.

and

. It is well known in the theory of Boolean

h

i

algebras (see [Rasiowa and Sikorski 1962]) that for every X

W . X is in

0

6

.

.

P iff

ff

X ⊆ (

X

Y

)

. . .

(

X

Y

)

.

.

n

n

[

6

0

0

[

6

for some X

" Y

" . . . " X

" Y

P and n

1. It follows that if X

P then

.

.

.

n

n

?

9

?

.

X ⊆ (X

Y

)

. . .

(X

Y

)

P

P"

.

.

n

n

.

(

0

0

(

?

ff

and so

P is closed under

in

W" R

and P coincides with the set of

.

.

upward closed sets in

P . Thus.

W" R"

P

is a partially ordered modal

.

.

h

i

frame4 we shall denote it by

. Moreover. we clearly have

. If

.

F

F

F

,.

h

i

⊆

2

M

F

V

M

F

V

.

.

⊆

"

is an intuitionistic model then

⊆

"

is a modal model

h

i

h

i

having

as its skeleton. So by the Skeleton Lemma.

M

M

M

.

(

" x)

⊆ . iff (

" x)

⊆ T (.)"

j

j

for every intuitionistic formula . and every point x in

.

F

It is worth noting that if

⊆

W" R

is a finite intuitionistic Kripke frame

F

then

is also a Kripke frame. However. for an infinite

.

is not in

.

F

F

F

.

h

i

general a Kripke frame. witness

' "

.

h

7i

The operator

is not the only one which. given an intuitionistic frame

.

.

F

returns a modal frame whose skeleton is isomorphic to

. As an example. we

F

define now an infinite class of such operators. For Kripke frames

⊆

W" R

F

and

⊆

V " S

. denote by

the

of

and

. i.e. the frame

direct product

G

F

G

F

G

h

i

W

V " R

S

in which the relation R

S is defined component-wise:

h

i

’

h

’

’

i

’

x

" y

(R

S )

x

" y

iff x

Rx

and y

S y

.

.

.

,

,

.

,

.

,

h

i

’

h

i

junctions8 However this di4erence is of no importance as far as embeddings into logics

in NExt

are concerned8

S.

ADVANCED MODAL LOGIC

55)

Let 0 5 k

' . We will regard k to be the set

0" . . . " k

1

if k 5 ' and

0" 1" . . .

if k ⊆ ' . Denote by

an operator which. given an intuitionistic

k

:

7

f

[

g

f

g

frame

⊆

W" R" P

. returns a modal frame

⊆

kW" kR" kP

such that

k

F

:

F

(i)

kW" kR

is the direct product of the k -point cluster

k " k

and

W" R

h

i

h

i

,

h

i

h

i

(in other words.

kW" kR

is obtained from

W" R

by replacing its every

.

:

point with a k -point cluster)4

h

i

h

i

(ii)

4

k

⊆

,:

F

F

2

(iii) I

X

kP . for every I

k and X

P .

.

For instance. we can take kP to be the Boolean closure of the set

’

?

ff

?

For a Kripke frame

⊆

W" R" UpW

we can. of course. take kP ⊆ 3

F

kW

I

X : I

k " X

P

.

.

f

’

ff

?

g

and then

⊆

kW" kR" 3

.

k

:

F

h

kW

i

.

:

:,. Canonical formulas

The language of canonical formulas. axiomatizing all si-logics and charac-

terizing the structure of their frames. can be easily developed following

the scheme of constructing the canonical formulas for

outlined in Sec-

K,

tion 1.6 and using the connection between modal and intuitionistic frames

established above. We confine ourselves here only to pointing out the dif-

ferences from the modal case and some interesting peculiarities4 details can

be found in [Zakharyaschev 1962. 1969] and [Chagrov and Zakharyaschev

1998].

Actually. there are two important differences. First. in the definition of

subreduction of

⊆

W" R" P

to

the condition (R2) does not correspond

F

G

to the fact that all sets in P are upward closed. We replace it by the

h

i

following condition

(R2

)

X

Q f

(X )

P .

.

5

.

)

?

; ?

where Q ⊆

V

X : X

Q

and P ⊆

W

X : X

P

. For a

completely defined f satisfying (R1) and (R3) the condition (R2

) is clearly

.

f

[

?

g

f

[

?

g

equivalent to (R2) and so every reduction is also a subreduction. If

is a

G

finite Kripke frame then (R2') is equivalent to

z

V f

(z )

P .

is

5

.

G

a

of

if

is a subframe of

and the identity map on V is a

subframe

F

G

.

.

F

)

?

; ?

subreduction of

to

. It is of interest to note that in the intuitionistic case

F

G

(cofinal) subreductions are dual to IC(N)-subalgebras of Heyting algebras

which preserve only implication. conjunction (and negation or

) but do

not necessarily preserve disjunction.

:

Second. we have to change the definition of open domains. Now we say

an antichain

(of at least two points) is an

in an intuitionistic

open domain

a

model

relative to a formula . if there ia a pair ta ⊆ (Φa "  a ) such that

N

Φa

 a ⊆

.

Φa

 a

and

Sub

Int

6

.

'?

V

W

550

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

1

3

2

p

p

q

p

p

r

-

-

q

'I

-

r

"(

-

o

o

o

"

-

'

"

'

"

G

'

"

'

"

'

"

p

q

p

q

r

-

. -

, -

o

-

. -

p

r

0

-

. -

Figure 15.

:

Φa iff a

⊆ : for all a

.

a

5

?

j

?

It is worth noting that in any intuitionistic model every antichain

is open

a

relative to every disjunction free formula . Indeed. let Φa be defined by

condition above and  a ⊆

.

Φa . It should be clear that :

?

Φa

Sub

iff :

Φa and ?

Φa . And if :

?

Φa . :

Φa but ?

 a then a

⊆ :

[

.

?

?

?

.

?

?

?

j

for every a

and b

⊆ ? for some b

. whence b

⊆ :

?. which is a

a

a

contradiction. It follows that

Φa

 a

.

Int

?

'j

?

'j

.

.

'?

V

W

EXAMPLE 2.3 Let us try to characterize the class of intuitionistic refuta-

tion frames for the

Weak Kreisel9Putnam Formula

wkp

⊆ (

p

q

r)

(

p

q)

(

p

r).

-

. -

, -

.

-

. -

,

-

. -

First we construct its simplest countermodel4 it is depicted in Fig. 15. where

by putting a formula to the left (right) of a point we mean that it is true

(not true) at the point. Then we observe that every frame

refuting

F

wkp

is cofinally subreducible to the frame

underlying this countermodel by

G

the map f defined as follows:

0

if x

⊆

p

q

r. x

⊆ (

p

q)

(

p

r)

1

if x

⊆

p

q

r. x

⊆

p and x

⊆ q

j

-

. -

, -

'j

-

. -

,

-

. -

j

-

. -

, -

j

-

j

1

ff

f (x) ⊆

ff

3

if x

⊆

p

q

r. x

⊆

p and x

⊆ r

2

if x

⊆ p or x

⊆

p

q

r

j

-

. -

, -

j

-

j

undefined otherwise.

j

j

-

. -

. -

ff

ff

9

ff

ff

ff

ff

8

However. the cofinal subreducibility to

is only a necessary condition for

G

F

wkp

⊆

. witness the frame having the form of the three-dimensional

'j

Boolean cube with the top point deleted. The reason for this is that the

antichain

1" 3

is a closed domain in

: it is impossible to insert a point

N

a between 0 and

1" 3

and extend to it consistently the truth-sets for the

f

g

depicted formulas. Indeed. otherwise we would have a

⊆

p

q

r.

f

g

a

⊆

q

r and so a

⊆

p. i.e. there must be a point x

a

such that

j

-

. -

, -

'j

-

, -

'j

-

?

3

ADVANCED MODAL LOGIC

55?

x

⊆ p. but such a point does not exist. In fact.

⊆

iff there is a

F

wkp

j

'j

cofinal subreduction of

to

satisfying (CDC) for

1" 3

.

F

G

ff

gg

Now. as in the modal case. with every finite rooted intuitionistic frame

F

D

⊆

W" R

and a set

of antichains in it we can associate two formulas

h

i

] (

"

"

) and ] (

"

). called the

and

canonical

negation free canonical

F

D

F

D

formulas

. respectively. so that

⊆ ] (

"

"

) (

⊆ ] (

"

)) iff there is a

G

F

D

G

F

D

:

(cofinal) subreduction of

to

satisfying (CDC) for

. For instance. if

G

F

D

'j

:

'j

a

" . . . " a

are all points in

and a

is its root. then one can take

.

n

.

F

] (

"

"

) ⊆

:

:d

:

p

"

ij

.

F

D

:

.

.

.

1

a

Ra

d

D

i

.

j

.

:

where

:

⊆ (

p

p

)

p

"

ij

k

j

i

a

Ra

.

j

k

9

.

.

:d ⊆

(

p

p

)

k

i

p

"

j

a

W

d

a

Ra

i

.

.

i

k

:

5

8

9

n

.

.

a

j

"

d

:

:

⊆

(

p

p

)

.

k

i

1

.

. :

i

5.

a

Ra

.

.

i

k

9

] (

"

) is obtained from ] (

"

"

) by deleting the conjunct :

.

F

D

F

D

:

1

THEOREM 2.2

.

There is an algorithm which. given an intuitionistic

. re5

turns canonical formulas

such that

] (

"

"

)" . . . " ] (

"

"

)

.

.

n

n

F

D

F

D

:

:

Int

Int

F

D

F

D

" . ⊆

" ] (

"

"

) " . . . " ] (

"

"

).

.

.

n

n

:

:

So the set of intuitionistic canonical formulas is complete for

: If

Ext

Int

.

is negation free then one can use only negation free canonical formulas:

And if

is disjunction free then al l

are empty:

.

i

D

Table 6 and Theorem 2.5 show canonical axiomatizations of the si-logics

in Table 7. Using this "geometrical" representation it is not hard to see. for

instance. that

. known as the

. is the greatest consistent

Smetanich logic

SmL

extension of

different from

4 it is the logic of the two-point rooted

Int

Cl

frame.

. the logic of the

. is character-

Weak Law of the Excluded Midd le

KC

ized by the class of directed frames. It is the greatest si-logic containing the

same negation free formulas as

(see [Jankov 1966a]).

. the

Dummett

Int

LC

or

. is characterized by the class of linear frames (see [Dum-

chain logic

mett 1979]).

and

are the minimal logics of depth n and width

n

n

BD

BW

n. respectively (see [Hosoi 1968] and [Smoryonski 1982]). Finite frames for

BTW

n

contain

n top points [Smoryonski 1982] and finite frames for

T

n

are of branching

n. i.e. no point has more than n immediate successors.

7

7

55fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

For

Int

⊆

" ] (

)

Cl

Int

⊆

" ] (

)

o

o

"

o

o

"

o

o

AK

.—

A

.

o

"

SmL

Int

⊆

" ] (

) " ] (

)

o

o

o

o

AK

.—

A

.

KC

Int

⊆

" ] (

"

)

LC

Int

⊆

" ] (

)

o

:

o

o

AK

.—

A

.

o

o

"

o

o

AK

.—

'

A

.

SL

Int

⊆

" ]

(

"

)

o

:

1 3

1 3

o o o

o o o

'I

"("

'I

"("

'

"

'

"

o

.—

AK

.

A

KP

Int

⊆

" ] (

"

1" 3

"

) " ] (

"

1" 3

"

)

o

ff

gg

:

o

ff

gg

:

n

o

.

"

.

.

1

o

"

BD

Int

n

⊆

" ] (

0

)

o

n

".

o 6 6 6 o

'I

"(

'

"

z '? "

BW

Int

n

⊆

" ] (

)

o

n

".

o 6 6 6 o

'I

"(

'

"

z '? "

BTW

Int

n

⊆

" ] (

"

)

o

:

n

".

o 6 6 6 o

'I

"(

'

z '? "

'

"

T

Int

n

⊆

" ]

(

)

o

n

".

o 6 6 6 o

'I

"(

'

z '? "

'

"

B

Int

n

⊆

" ]

(

"

)

o

:

Table 6. Canonical axioms of standard superintuitionistic logics

ADVANCED MODAL LOGIC

55'

THEOREM 2.5 (Nishimura 1960. Anderson 1983)

L

Every extension

of

Int

by formulas in one variable can be represented either as

L ⊆

"

⊆

" ]

(

"

)

n

Int

nf

Int

H

,

n

'

:

or as

L ⊆

"

⊆

" ]

(

"

) " ]

(

"

)"

Int

nf

Int

H

H

n

".

n

",

,

.

n

5

:

:

'

'

where

.

.

are the subframes of the frame in Fig: 8fl generated

n

n

n

".

",

H

H

H

by the points

.

and

n

n " 1

n " 3

. respectively. and

is an abbreviation

]

(

"

)

'

F

for

] (

"

"

)

.

the set of al l antichains in

:

F

D

D

F

'

'

:

:

Jankov [1969] proved in fact that logics of the form

" ]

(

"

) and

Int

F

'

only them are splittings of Ext

. However. not every si-logic is a union-

Int

:

splitting of Ext

which means that this class has no axiomatic basis.

Int

:,: Modal companions and preservation theorems

The fact that the G;odel translation T embeds

into

and the relation-

Int

S,

ship between intuitionistic and modal frames established in Section 2.1 can

be used to reduce various problems concerning

(e.g. proving complete-

Int

ness or FMP) to those for

and vice versa. Moreover. it turns out that

S,

each logic in Ext

is embedded by T into some logics in NExt

. and for

Int

S,

each logic in NExt

there is one in Ext

embeddable in it.

S,

Int

We say a modal logic M

NExt

is a

of a si-logic L

modal companion

S,

if L is embedded in M by T . i.e. if for every intuitionistic formula .

?

.

L iff T (.)

M .

?

?

If M is a modal companion of L then L is called the

of M

siffifragment

and denoted by

M . The reason for denoting the operator "modal logic

,

its si-fragment" by the same symbol we used for the skeleton operator is

".

explained by the following

THEOREM 2.7

For every

.

: More5

M

NExt

M ⊆

. : T (.)

M

S,

,

over. if

is characterized by a class

of modal frames then

is char5

M

M

,

?

f

?

g

acterized by the class

of intuitionistic frames:

⊆

:

,

,

F

F

C

C

f

? C g

Proof

,

It suffices to show that

. : T (.)

M

⊆ Log

. Suppose that

T (.)

M . Then

⊆ T (.) and so. by the Skeleton Lemma.

⊆ . for

F

,

F

f

?

g

C

?

j

j

every

. i.e. .

Log

. Conversely. if

⊆ . for all

then. by

F

,

,

F

F

the same lemma. T (.) is valid in all frames in

and so T (.)

M .

.

? C

?

C

j

? C

C

?

Thus.

maps NExt

into Ext

. The following simple observation

,

S,

Int

shows that actually

is a surjection. Given a logic L

Ext

. we put

,

Int

:

S,

L ⊆

T (.) : .

L

.

" f

?

g

?

5ff[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 2.6 (Dummett and Lemmon 1979)

For every siffilogic

L

.

L

is

:

a modal companion of

L

:

Proof

,:

Clearly. L

L. To prove the converse inclusion. suppose .

L.

i.e. there is a frame

for L refuting . Since

. by the Skeleton

F

F

F

,.

ff

'?

⊆

2

Lemma we have

⊆

L and

⊆ T (.). Therefore. T (.)

L and so

.

:

.

:

F

F

j

'j

'?

.

.

L.

,:

'?

Now we use the language of canonical formulas to obtain a general char-

acterization of all modal companions of a given si-logic L. Our presentation

follows [Zakharyaschev 1969. 1991]. Notice first that for every modal frame

G

F

D

G

F

D

and every intuitionistic canonical formula ] (

"

"

).

⊆ —(

"

"

) iff

,

S,

S,

G

F

D

F

D

F

D

⊆ ] (

"

"

) and so

T (] (

"

"

)) ⊆

—(

"

"

). The same

:

j

:

j

:

"

:

"

:

concern. of course. the negation free canonical formulas.

THEOREM 2.8

M

NExt

A logic

is a modal companion of a siffilogic

S,

L ⊆

"

] (

"

"

) : i

I

M

i,

can be represented in the form

i

i

Int

F

D

?

f

:

?

g

M ⊆

—(

"

"

) : i

I

—(

"

"

) : j

J

"

i

i

j

j

S,

F

D

F

D

" f

:

?

g " f

:

?

g

where every frame

. for

. contains a proper cluster:

j

j

J

F

?

Proof

(

) We must show that for every intuitionistic formula . .

L

iff T (.)

M . Suppose that .

L and

⊆

W" R" P

is a frame separating

F

⊆

?

. from L. We prove that

separates T (.) from M . As was observed

.

F

?

'?

h

i

above.

⊆ T (.) and

⊆ —(

"

"

) for any i

I . So it remains to

i

i

.

F

.

F

F

D

show that

⊆ —(

"

"

) for every j

J .

j

j

.

F

F

D

'j

j

:

?

j

:

?

Suppose otherwise. Then. for some j

J . we have a subreduction f of

.

F

F

to

. Let a

and a

be distinct points belonging to the same proper

j

.

,

?

cluster in

. By the definition of subreduction. f

(a

)

f

(a

)

and

j

5

5

.

,

F

.

.

.

.

ff

;

f

(a

)

f

(a

)

. and so there is an infinite chain x

Ry

Rx

Ry

R . . . in

5

5

,

.

.

.

,

,

.

F

such that

x

" x

" . . .

f

(a

) and

y

" y

" . . .

f

(a

). And since

.

,

.

.

,

,

5

5

ff

;

.

.

R is a partial order. all the points x

and y

are distinct.

i

i

f

g ff

f

g ff

Since f

(a

)

P . there are X

" Y

P such that

5

.

i

i

.

.

?

?

.

f

5

(a

) ⊆ (

X

Y

)

. . .

(

X

Y

).

.

.

.

n

n

[

6

0

0

[

6

And since f

(a

)

f

(a

) ⊆

. for every point y

there is some number n

5

5

.

,

i

i

.

.

such that y

X

and y

Y

. But then. for some distinct l and m. the

i

n

i

n

i

i

0

fl

numbers n

and n

must coincide. and so if. say. y

Ry

then x

Y

and

l

m

l

m

m

n

?

'?

m

'?

.

x

X

(for y

Rx

Ry

. X

⊆ X

. Y

⊆ Y

). Therefore. x

f

(a

).

m

n

l

m

m

i

i

i

i

m

5

.

l

?

3

3

'?

which is a contradiction.

The rest of the proof presents no difficulties.

.

ADVANCED MODAL LOGIC

5ff5

This proof does not touch upon the cofinality condition. So along with

canonical formulas in Theorem 2.8 we can use negation free canonical for-

mulas. Thus. we have:

,S,

,S,

:

,Dum

,Grz

Int

⊆

.

⊆

⊆

⊆

"

,S,

"

,

S,

"

Grz

KC

.

⊆

(

.

) ⊆

"

"

,S,

5

,

S,

5

Grz

LC

.

⊆

(

.

) ⊆

"

"

,S.

,

S.

Grz

Cl

⊆

(

) ⊆

.

"

COROLLARY 2.6

The set of modal companions of every consistent siffilogic

L

forms the interval

.

,

:

:

S,

:

:

Grz

5

(L) ⊆ [

L"

L

—(

)] ⊆

M

NExt

:

L

M

L

"

f

?

ff

ff

"

g

.

.

o o

and contains an in.nite descending chain of logics:

,

:

Proof

Grz

F

D

F

D

F

Notice first that —(

"

"

) and —(

"

) are in

iff

contains

a proper cluster. So

(L)

[

L.

L

—(

)]. On the other hand. the

,

:

:

5

.

:

ff

"

.

.

o o

si-fragments of all logics in the interval are the same. namely L. Therefore.

,

:

.

,

:

:

(L) ⊆ [

L"

L

—(

)]. Now. if L is consistent then ] (

)

L and so

5

"

o

'?

.

.

o o

we have

,

:

:

:

:

:

For

L

. . .

L

—(

)

. . .

L

—(

)

L

—(

) ⊆

"

C

C

C

n

,

.

—

—

"

—

—

"

—

"

where

is the non-degenerate cluster with i points.

i

C

.

This result is due to Maksimova and Rybakov [1985]. Blok [1986] and

Esakia [1989b].

Thus. all modal companions of every si-logic L are contained between the

least companion

L and the greatest one. viz.

L

—(

). which will be

:

:

denoted by

L. Using Theorems 2.8 and 1.55. we obtain

.

,

:

"

.

.

o o

COROLLARY 2.9

There is an algorithm which. given a modal formula

.

.

returns an intuitionistic formula

such that

:

:

(

.) ⊆

" :

,

S,

Int

"

The following theorem. which is also a consequence of Theorem 2.8. de-

scribes lattice-theoretic properties of the maps

.

and

. Items (i). (ii)

,

:

.

and (iv) in it were first proved by Maksimova and Rybakov [1985]. and (iii)

is due to Blok [1986] and Esakia [1989b] and known as the Blok!Esakia

Theorem.

5ffff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 2.10 (i)

The map

is a homomorphism of the lattice

,

NExt

S,

onto the lattice

:

Ext

Int

(ii)

Ext

NExt

The map

is an isomorphism of

into

:

:

Int

S,

(iii)

Ext

NExt

The map

is an isomorphism of

onto

:

.

Int

Grz

(iv)

Al l these maps preserve in.nite sums and intersections of logics:

Now we give frame-theoretic characterizations of the operators

and

.

:

.

Note first that the following evident relations between frames for si-logics

and their modal companions hold:

F

F

F

F

⊆

M iff

⊆ M "

⊆ L iff

⊆

L"

,

.

.

.

j

j

j

j

,

:

:

:

F

F

F

F

⊆ L iff

⊆

L"

⊆ L iff

⊆

L.

k

j

j

j

j

THEOREM 2.11 (Maksimova and Rybakov 1985)

L

A siffilogic

is charac5

terized by a class

of intuitionistic frames i,

is characterized by the

L

.

class

:

⊆

:

.

.

F

F

C

C

f

? C g

Proof

F

D

.

(

) It suffices to show that any canonical formula —(

"

"

)

L

is refuted by some frame in

. Since

is partially ordered. ] (

"

"

)

L.

.

F

F

D

8

:

'?

i.e. there is

refuting ] (

"

"

) and so

⊆ —(

"

"

). (

) is

F

F

D

F

F

D

.

C

:

'?

straightforward.

.

? C

:

'j

:

⊆

To characterize

we require

:

LEMMA 2.13

—(

"

"

)

For any canonical formula

built on a quasiffiordered

F

D

frame

.

. where

and

—(

"

"

)

—(

"

"

)

⊆

:

S,

,

,

,

,

F

F

D

F

D

D

d

d

D

:

:

?

"

:

f

?

g

,

d

⊆

C (x) : x

d

:

f

?

g

Proof

G

F

D

Let

be a quasi-ordered frame refuting —(

"

"

). Then there is

a cofinal subreduction f of

to

satisfying (CDC) for

. The map h from

G

F

D

:

F

F

,

F

onto

defined by h(x) ⊆ C (x). for every x in

. is clearly a reduction

of

to

. So the composition hf is a cofinal subreduction of

to

. and

F

F

,

G

F

,

it is easy to verify that it satisfies (CDC) for

.

,

D

.

THEOREM 2.12

L

A siffilogic

is characterized by a class

of frames i,

:

L

is characterized by the class

. where

:

⊆

:

k

k

k

:

:

:

F

F

C

.

.k.,

S

C

C

f

? C g

Proof

F

:

F

(

) As was noted above. if

is a frame for L then

is a frame for

k

L. So suppose that a formula —(

"

"

). built on a quasi-ordered frame

F

D

8

⊆

W" R

. does not belong to

L and show that it is refuted by some frame

:

:

:

F

h

i

in

. By Lemma 2.13. —(

"

"

)

L and so ] (

"

"

)

:

,

,

:

,

,

F

D

F

D

.

.k.,

k

L. Hence there is a frame

⊆

V " S" Q

in

which refutes ] (

"

"

).

G

,

,

F

D

S

C

:

'?

:

'?

But then

⊆

L and

⊆ —(

"

"

). Let f be a subreduction

.

:

.

,

,

G

G

F

D

h

i

C

:

of

to

satisfying (CDC) for

and let k ⊆ max

C (x)

: x

W

.

.

,

G

F

,

D

j

'j

:

fj

j

?

g

ADVANCED MODAL LOGIC

5ff—

Define a partial map h from

⊆

kV " kS" kQ

onto

as follows: if x

V .

k

:

G

F

y

W . f (x) ⊆ C (y

) and C (y

) ⊆

y

" . . . " y

then we put h(

i" x

) ⊆ y

.

n

i

.

.

.

.

h

i

?

?

f

g

h

i

for i ⊆ 0" . . . " n. By the definition of

. for any i

0" . . . " n

we have

k

:

.

.

.

? f

g

h5

(y

) ⊆

i" x

: x

f 5

(C (y

))

⊆

i

f 5

(C (y

))

kQ.

i

.

.

fh

i

?

g

f

g ’

?

Now. one can readily prove that h is a cofinal subreduction of

to

k

:

G

F

satisfying (CDC) for

. So

⊆ —(

"

"

). (

) is obvious.

k

D

G

F

D

:

.

'j

:

⊆

It is worth noting that this proof will not change if we put in it k ⊆ ' .

COROLLARY 2.15

L

Ext

A logic

is characterized by a class

of

Int

frames i,

is characterized by the class

:

L

:

:

,

C

?

C

The following theorem provides a deductive characterization of the maps

:

.

and

.

THEOREM 2.17

L

For every siffilogic

and every modal canonical formula

—(

"

"

)

built on a quasiffiordered frame

.

F

D

F

:

(i) —(

"

"

)

L

] (

"

"

)

i,

L

'

F

D

F

D

:

,

,

(ii) —(

"

"

)

L

] (

"

"

)

L

i, either

is partial ly ordered and

.

F

D

F

F

D

:

?

:

?

or

contains a proper cluster:

F

:

?

:

?

Proof

(i) The implication (

) was actually established in the proof of

Theorem 2.12. and the converse one follows from Lemma 2.13.

8

(ii) Suppose —(

"

"

)

L. Then either

is partially ordered. and so

F

D

F

.

] (

"

"

)

L. or

contains a proper cluster. The converse implication

F

D

F

:

?

follows from (i) and the fact that —(

"

"

)

for every frame

with

F

D

F

Grz

:

?

a proper cluster.

:

?

.

The results obtained in this section not only establish some structural

correspondences between logics in Ext

and NExt

and their frames.

Int

S,

but may be also used for transferring various properties of modal logics

to their si-fragments and back. A few results of that sort are collected in

Table 84 we shall cite them as the Preservation Theorem. The preservation

of decidability follows from the definition of

and Theorem 2.17. That

,

,

preserves Kripke completeness. FMP and tabularity is a consequence of

Theorem 2.7. The map

preserves Kripke completeness and FMP. since

:

we can define

in Theorem 2.12 so that

W" R

⊆

kW" kR

4 however.

k

k

:

:

:

: Cl

S.

does not in general preserve the tabularity. because

⊆

is not

h

i

h

i

tabular. The preservation of FMP and tabularity under

follows from

.

Theorem 2.11. On the other hand. Shehtman [1960] proved that

does not

.

preserve Kripke completeness (since

preserves it and

is complete.

:

Grz

this means in particular that Kripke completeness is not preserved under

sums of logics in NExt

). Some other preservation results in Table 8 will

S,

be discussed later. For references see [Chagrov and Zakharyaschev 1993.

1998].

5ff(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Property of logics

Preserved under

,

:

.

Decidability

Yes Yes Yes

Kripke completeness

Yes Yes No

Strong completeness

Yes Yes No

Finite model property

Yes Yes Yes

Tabularity

Yes No Yes

Pretabularity

Yes No Yes

-persistence

Yes Yes No

D

Local tabularity

Yes No

No

Disjunction property

Yes Yes Yes

Halldoen completeness

Yes No

No

Interpolation property

Yes No

No

Elementarity

Yes Yes No

Independent axiomatizability No Yes Yes

Table 8. Preservation Theorem

:," Completeness

In this section we briefly discuss the most important results concerning

completeness of si-logics with respect to various classes of Kripke frames.

Kripke completeness

That not all si-logics are complete with respect

to Kripke frames was discovered by Shehtman [1988]. who found a way

to adjust Fine's [1985b] idea to the intuitionistic case (which was not so

easy because intuitionistic formulas do not "feel" infinite ascending chains

essential in Fine's construction4 see Section 30 of

). Note

Basic Modal Logic

however that Kuznetsov's [1987] question whether all si-logics are complete

with respect to the topological semantics (see

) is still

Intuitionistic Logic

open.

As to general positive results. notice first that the Preservation Theorem

yields the following translation of Fine's [1985c] Theorem on finite width

logics (si-logics of finite width were studied by Sobolev [1988a]).

THEOREM 2.16

n

Ext

Every siffilogic of width

?i:e:. a logic in

' see

BW

n

Table ff" is characterized by a class of Noetherian Kripke frames of width

n

:

7

The translation of Sahlqvist's Theorem gives nothing interesting for si-

logics. A sort of intuitionistic analog of this theorem has been recently

ADVANCED MODAL LOGIC

5ff)

proved by Ghilardi and Meloni [1998]. Here is a somewhat simplified variant

of their result in which p. q . r. s denote tuples of propositional variables

and : . ? tuples of formulas of the same length as r and s. respectively.

THEOREM 2.18 (Ghilardi and Meloni 1998)

.(p" q " r " s)

Suppose

is an in5

tuitionistic formula in which the variables

occur positively and the vari5

r

ables

occur negatively. and which does not contain any

. except for

s

negations and double negations of atoms. in the premise of a subformula of

.

the form

: Assume also that

.

.

.

.

:(p" q)

?(p" q)

and

are formulas such

that

occur positively in

and negatively in

. while

occur negatively in

p

:

?

q

.

:

?

and positively in

: Then the logic

Int

" .(p" q " :(p" q)" ?(p" q))

is canonical:

The preservation of

-persistence under

(see [Zakharyaschev 1996])

,

and the fact (discovered by Chagrova [1990]) that

L is characterized by an

:

D

elementary class of Kripke frames whenever L is determined by such a class

provide us with an intuitionistic variant of the Fine!van Benthem Theorem.

THEOREM 2.16

If a siffilogic is characterized by an elementary class of

Kripke frames then it is

5persistent:

D

As in the modal case. it is unknown whether the converse of this theo-

rem holds. All known non-elementary si-logics. for instance the Scott logic

SL

T

and the logics

of finite n-ary trees (see [Rodenburg 1966]) are not

n

canonical and even strongly complete either. as was shown by Shimura

[1997]. (Actually he proved that no logic in the intervals [

"

"

] and

SL

SL

bd

:

Int

T

Int

[

"

]. save of course

. is strongly complete.)

,

As far as we know. there are no examples of si-logics separating canonicity.

-persistence and strong completeness. (Ghilardi. Meloni and Miglioli have

D

recently showed that

in any language with finitely many variables is

SL

canonical). Theorem 1.50 which holds in the intuitionistic case as well gives

an algebraic counterpart of strong Kripke completeness.

The 1nite model property

The first example of an infinitely axiomati-

zable si-logic without FMP was constructed by Jankov [1966b]—that was in

fact the starting point of a long series of "negative" results in modal logic.

A finitely axiomatizable logic without FMP appeared two years later in

[Kuznetsov and Gerchiu 1980]. The reader can get some impression about

5ff0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

this and other examples of that sort by proving (it is really not hard) that

1 3

1 3

o

"

o

"

o o o o

o o o o

'I

"(

BM

]7

'I

"(

BM

]7

'

B

]

"

'

B

]

"

. ⊆ ] (

) ,

L ⊆

"

" ] (

"

1" 3

)

Int

bw

'

o

?

o

ff

gg

but no finite frame can separate . from L. (Notice by the way that

L

:

is axiomatizable by Sahlqvist formulas4 see [Chagrov and Zakharyaschev

1997b].)

FMP of a good many si-logics was proved using various forms of filtration4

see e.g. [Gabbay 1980]. [Ono 1983]. [Smoryonski 1982]. [Ferrari and Miglioli

1992]. As an illustration of a rather sophisticated selective filtration we

present here the following

THEOREM 2.19 (Gabbay and de Jongh 1985)

The logic

?see Table ff"

T

n

is characterized by the class of .nite

5ary trees:

n

Proof

T

First we prove that

is characterized by the class of finite frames

n

of branching

n. Suppose .

and

⊆

"

is a model for

n

T

M

F

V

T

n

refuting . Without loss of generality we may assume that

⊆

W" R

is a

F

7

'?

h

i

tree. Let # ⊆

. and Φ

⊆

:

# : x

⊆ :

. for every point x in

.

x

Sub

h

i

F

Given x in

. put rg(x) ⊆

[y ] : y

x

and say that x is of

minimal range

F

f

?

j

g

if rg(x) ⊆ rg(y) for every y

[x]

x

. Since there are only finitely many

f

?

3g

distinct #-equivalence classes in

. every y

[x] sees a point z

[x] of

?

0

3

M

minimal range. Now we extract from

a finite refutation frame

⊆

V " S

M

G

?

?

for . of branching

n. To begin with. we select some point x of minimal

h

i

range at which . is refuted and put V

⊆

x

.

.

7

f

g

Suppose V

has already been defined. If

rg(x)

⊆ 1 for every x

V

. then

k

k

we put

⊆

V " S

. where V ⊆

V

and S is the restriction of R to V .

G

i

5.

k

h

i

Otherwise. for each x

V

with

rg(x)

" 1 and each [y ]

rg(x) different

k

S

k

j

j

?

from [x] and such that Φ

Φ

for no [z ]

rg(x)

[x]

. we select a point

z

y

?

j

j

?

u

[y ]

x

of minimal range. Let U

be the set of all selected points for x

x

—

?

[ f

g

?

0

3

and V

⊆

U

. It should be clear that Φ

Φ

(and rg(x)

rg(u)). for

k

".

x

x

x

u

every u

U

. and so the inductive process must terminate. Consequently

—

(

x

S

?

G

⊆ .

'j

It remains to establish that

⊆

. i.e.

is of branching

n. Suppose

n

G

G

T

otherwise. Then there is a point x in

with m

n"1 immediate successors

G

j

7

x

" . . . " x

. which are evidently in U

because

is a tree. We are going to

.

m

x

9

F

construct a substitution instance of

's axiom

which is refuted at x

n

n

T

bb

in

.

M

Denote by 9

the conjunction of the formulas in Φ

. Since all of them

i

x

i

are true at x

in

. we have x

⊆ 9

4 and since Φ

Φ

for no distinct i and

i

i

i

i

j

M

j

ff

ADVANCED MODAL LOGIC

5ff?

j . we have x

⊆ ?

if i

⊆ j . Put ?

⊆ 9

. for 0

i 5 n. ?

⊆ 9

. . .

9

j

i

i

i

n

n

m

and consider the truth-value of the formula : ⊆

?

,p

" . . . " ?

,p

at

bb

n

n

n

.

.

'j

7

,

,

x in

.

M

f

g

n

Since xRx

for every i ⊆ 0" . . . " m. we have x

⊆

?

. Suppose that

i

i

n

i

5.

'j

x

⊆

((?

i

?

)

j

?

). Then y

⊆ ?

?

and

j

i

j

i

5.

i

j

5

i

j

5

W

i

j

5

'j

.

.

j

.

y

⊆

?

. for some y

x

and some i

0" . . . " n

. and hence y

⊆ ?

.

j

i

V

W

W

W

i

j

5

'j

?

3

? f

g

'j

Since x

⊆ ?

and x

⊆

?

. y sees no point in [x

] and so y

x (for

i

i

i

j

i

?

W

i

j

5

j

'j

'2

otherwise x would not be of minimal range). Therefore. Φ

Φ

for some

W

x

y

j

j

0" . . . " m

. and then y

⊆ ?

if j 5 n and y

⊆ ?

if j

n. which is a

j

n

ff

? f

g

j

j

9

contradiction.

n

It follows that x

⊆

((?

?

)

?

). from which x

⊆ : .

i

j

j

i

5.

i

j

5

i

j

5

contrary to

being a model for

. It remains to notice that every finite

n

M

bb

V

W

W

j

.

.

'j

frame of branching

n is a reduct of a finite n-ary tree. which clearly

validates

.

n

T

7

.

Another way of obtaining general results on FMP of si-logics is to trans-

late the corresponding results in modal logic with the help of the Preserva-

tion Theorem.

THEOREM 2.30

Every siffilogic of .nite depth ?i:e:. every logic in

Ext

BD

n

.

for

" is local ly tabular:

n 5 '

Note. however. that unlike NExt

. the converse does not hold: the

K,

Dummett logic

. characterized by the class of finite chains (or by the

LC

infinite ascending chain). is locally tabular. As we saw in Section 1.8. every

non-locally tabular in NExt

logic is contained in

. the only

pre5

S,

Grz.5

local ly tabular logic

in NExt

. But in Ext

this way of determining

S,

Int

local tabularity does not work:

THEOREM 2.31 (Mardaev 1965)

There is a continuum of preffilocal ly tab5

ular logics in

:

Ext

Int

Besides. it is not clear whether every locally tabular logic in Ext

(or

Int

NExt

) is contained in a pre-locally tabular one.

K,

An intuitionistic formula is said to be

if every occur-

essential ly negative

rence of a variable in it is in the scope of some

. If . is essentially negative

then T (.) is a

-formula. which yields

.,

-

THEOREM 2.33 (McKay 1981. Rybakov 1986)

L

If a siffilogic

is decidable

?or has FMP" and

is an essential ly negative formula then

is decidable

.

L".

?has FMP":

Originally this result was proved with the help of Glivenko's Theorem

(see Section 8 in

). Say that an occurrence of a variable

Intuitionistic Logic

'
"
"
"
"
"
"
"
5fffl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

in a formula is

if it is not in the scope of any

. A formula

essential

. is

if every two essential occurrences of the same variable in . are

mild

-

either both positive or both negative. Kuznetsov [1983] claimed (we have

not seen the proof ) that all si-logics whose extra axioms do not contain

negative occurrences of essential variables have FMP. And Wroonski [1969]

announced that if L is a decidable si-logic and . a mild formula then L " .

is also decidable.

Subframe and cofinal subframe si-logics—that is logics axiomatizable by

canonical formulas of the form ] (

) and ] (

"

). respectively—can be char-

F

F

acterized both syntactically and semantically (see [Zakharyaschev 1996]).

:

THEOREM 2.32

The fol lowing conditions are equivalent for every siffilogic

L

"

(i) L

is a ?co.nal" subframe logic'

(ii) L

is axiomatizable by implicative ?respectively. disjunction free" for5

mulas'

(iii) L

is characterized by a class of .nite frames closed under the forma5

tion of ?co.nal" subframes:

That all si-logics with disjunction free axioms have FMP was first proved

by McKay [1966] with the help of Diego's [1966] Theorem according to which

there are only finitely many pairwise non-equivalent in

disjunction free

Int

formulas in variables p

" . . . " p

(see also [Urquhart 1985]).

.

n

Since frames for

contain no clusters. Theorem 1.76 and its analog

Int

for cofinal subframe logics reduce in the intuitionistic case to the following

result which is due to Chagrova [1966]. Rodenburg [1966]. Shimura [1992]

and Zakharyaschev [1996].

THEOREM 2.35

Al l siffilogics with disjunction free axioms are elementary

?de.nable by

5sentences" and

5persistent:

)1

D

Theorem 1.66 is translated into the intuitionistic case simply by replacing

K,

Int

with

.

with " and — with ] . As a consequence we obtain. for

instance. that Ono's [1983]

and all other logics whose canonical axioms

n

B

"

are built on trees have FMP. Moreover. we also have

THEOREM 2.37 (Sobolev 1988b. Nishimura 1960)

Al l siffilogics with extra

axioms in one variable have FMP and are decidable:

In fact Sobolev [1988b] proved a more general (but rather complicated)

syntactical sufficient condition of FMP and constructed a formula in two

variables axiomatizing a si-logic without FMP (Shehtman's [1988] incom-

plete si-logic has also axioms in two variables).

ADVANCED MODAL LOGIC

5ff'

Tabularity

By the Blok!Esakia and Preservation Theorems. the situation

with tabular logics in Ext

is the same as in NExt

. In particular.

Int

Grz

L

Ext

is tabular iff

"

L for some n 5 ' iff L is not a

n

n

Int

BD

BW

?

ff

sublogic of one of the three pretabular logics in Ext

. namely

.

Int

LC

BD

,

and

"

.

(The pretabular si-logics were described by Maksimova

KC

bd

:

[1983].) The tabularity problem is decidable in Ext

.

Int

:,5 Disjunction property

One of the aims of studying extensions of

. which may be of interest

Int

for applications in computer science. is to describe the class of constructive

si-logics. At the propositional level a logic L

Ext

is regarded to be

Int

constructive if it has the

(DP. for short) which means

disjunction property

?

that for all formulas . and : .

.

:

L implies .

L or :

L.

,

?

?

?

That intuitionistic logic itself is constructive in this sense was proved in a

syntactic way by Gentzen [1925!1927]. However. (Lukasiewicz (1973) con-

jectured that no proper consistent extension of

has DP.

Int

A similar property was introduced for modal logics (see e.g.

[Lemmon

and Scott 1988]): L

NExt

has the

if. for

?modal" disjunction property

K

every n

1 and all formulas .

" . . . " .

.

.

n

?

9

.

.

.

. . .

.

L implies .

L. for some i

1" . . . " n

.

.

n

i

,

,

?

?

? f

g

The following theorem (in a somewhat different form it was proved in

[Hughes and Cresswell 1965] and [Maksimova 1966]) provides a semantic

criterion of DP.

THEOREM 2.36

L

Suppose a modal or siffilogic

is characterized by a class

of descriptive rooted frames closed under the formation of rooted generated

C

subframes: Then

has DP i,. for every

and al l

L

n

1

" . . . "

with

.

n

F

F

roots

. there is a frame

for

with root

such that the disjoint

x

" . . . " x

L

x

.

n

F

9

? C

union

is a generated subframe of

with

.

" . . . "

n

x

" . . . " x

x

:

.

n

F

F

F

f

g ff

3

Proof

F

We consider only the modal case. (

) Let

⊆

W

" R

" P

be

L

L

L

L

a universal frame for L. big enough to contain

" . . . "

as its generated

.

n

F

F

8

h

i

subframe. Assuming that

is associated with a suitable canonical model

L

F

for L. we show that there is a point x in

such that x

⊆ W

. The set

L

L

F

 . ⊆

. :

y

W

y

⊆ .

L

.

f-

1

?

'j

g

3

is L-consistent (for otherwise

.

. . .

.

L for some .

" . . . " .

L).

.

.

n

n

.

.

Let   be a maximal L-consistent extension of

and x the point in

.

L

F

,

,

?

'?

where   is true. Then xR

y . for every y

W

.

L

L

?

5—[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

(

) Suppose otherwise. Then there are formulas .

" . . . " .

L such

.

n

⊆

'?

that

.

. . .

.

L. Take frames

" . . . "

refuting .

" . . . " .

.

.

.

n

n

n

.

.

F

F

at their roots. respectively. and let

be a rooted frame for L containing

F

,

,

?

? C

F

F

.

n

" . . . "

as a generated subframe and such that its root x sees the roots

of

" . . . "

. Then all the formulas

.

" . . . "

.

are refuted at x and so

.

n

.

n

F

F

.

.

.

.

.

.

. . .

.

L. which is a contradiction.

.

n

,

,

'?

It should be clear that if we use only the sufficient condition of Theo-

rem 2.36. the requirement that frames in

are descriptive is redundant.

Furthermore. it is easy to see that for L

NExt

we may assume n

3.

K,

C

And clearly a logic L

NExt

has DP iff. for all . and : .

.

:

L

S,

?

7

.

.

?

,

?

implies

.

L or

:

L.

.

.

?

?

As a direct consequence of the proof above we obtain

COROLLARY 2.38

L

A modal or siffilogic

has DP i, the canonical frame

F

L

L

L

⊆

W

" R

x

x

⊆ W

contains a point

such that

L

:

h

i

3

Using the semantic criterion above it is not hard to show that DP is

preserved under

.

and

. It is also a good tool for proving and disproving

,

:

.

DP of logics with transparent semantics.

EXAMPLE 2.36 (i) Let

" . . . "

be serial rooted Kripke frames. Then

.

n

F

F

the frame obtained by adding a root to

" . . ."

is also serial. Therefore.

.

n

F

F

D

K

K,

T

S,

Grz

GL

has DP. In the same way one can show that

.

.

.

.

.

and many other modal logics have DP.

(ii) Since no rooted symmetrical frame can contain a proper generated

subframe. no consistent logic in NExt

has DP.

KB

The first proper extensions of

with DP were constructed by Kreisel

Int

and Putnam [1978]: these were

(now called the

Kreisel9Putnam logic

KP

and

(known as the

). We present here Gabbay's [1980] proof

Scott logic

SL

that

has DP.

KP

THEOREM 2.39 (Kreisel and Putnam 1978)

KP

has DP:

Proof

KP

Using filtration one can show that

is characterized by the class

of finite rooted frames

⊆

W" R

satisfying the condition

F

h

i

x" y " z (xRy

xRz

yRz

zRy

u (xRu

uRy

uRz

)

.

. -

. -

. 1

.

.

.

v (uRv

w (vRw

(yRw

zRw))))).

(17)

)

. 1

.

,

If

is such a frame then for each non-empty X

W

. the generated

,

F

.

subframe of

based on the set W

(W

X )

is rooted4 we denote its

,

F

.

ff

root by r(X ).

[

[

;

ADVANCED MODAL LOGIC

5—5

Let

⊆

W

" R

and

⊆

W

" R

be finite rooted frames satisfying

.

.

.

,

,

,

F

F

(17). We construct from them a frame

⊆

W" R

by taking

F

h

i

h

i

h

i

W ⊆ W

W

U"

.

,

6

6

.

.

where U ⊆

X

X

: X

W

" X

W

" X

" X

⊆

. and

,

,

.

,

.

,

.

,

.

,

f

6

ff

ff

flg

xRy

iff (x" y

W

xR

y)

(x" y

U

x

y)

i

i

?

.

,

?

.

(

,

(x ⊆ X

X

U

y

W

r(X

)R

y).

.

,

i

i

i

6

?

.

?

.

It follows from the given definition that

"

is a generated subframe of

.

,

F

F

F

F

,

,

. W

W

is a cover for

and W

W

is its root. So our theorem

.

,

.

,

.

.

will be proved if we show that (17) holds.

6

6

Suppose x" y " z

W satisfy the premise of (17). Since (17) holds for

F

.

F

?

and

. we can assume that x ⊆ X

X

U . Let Y

Y

and Z

Z

be

,

.

,

.

,

.

,

the sets of final points in y

and z

. respectively. with Y

" Z

W

. By the

i

i

i

6

?

6

6

definition of R. we have Y

" Z

X

. Consider u ⊆ (Y

Z

)

(Y

Z

).

i

i

i

.

.

,

,

3

3

ff

Clearly. xRu. uRy and uRz . Suppose now that v

u

. Let w be any final

ff

6

6

6

point in v

. Then v

(Y

Z

)

(Y

Z

) and so either yRw or zRw.

.

.

,

,

?

3

3

?

6

6

6

.

Other examples of constructive si-logics were constructed by Ono [1983]

and Gabbay and de Jongh [1985]. namely.

and

. Anderson [1983]

n

n

B

T

proved that among the consistent si-logics with extra axioms in one variable

only those of the form

"

. for n

7. have DP (for n ⊆ 6 the

Int

nf

,

",

n

9

proof was found by Wroonski [1985]4 see also [Sasaki 1993]). Finally. Wroonski

[1982] showed that there is a continuum of si-logics with DP.

The additional axioms of logics in all these examples contained occur-

rences of

4 on the other hand. known examples of si-logics with disjunction

free extra axioms. say

.

.

.

or

. were not constructive.

n

n

LC

KC

Cl

BW

BD

,

This observation led Hosoi and Ono [1982] to the conjecture that the dis-

junction free fragment of every consistent si-logic with DP coincides with

that of

. We present a proof of this conjecture following [Zakharyaschev

Int

1968].

First we describe the cofinal subframe logics in NExt

with DP. as-

S,

suming that every such logic L is represented by its independent canonical

axiomatization

L ⊆

—(

"

) : i

I

.

(16)

i

S,

F

" f

:

?

g

All frames in the rest of this section are assumed to be quasi-ordered.

Say that a finite rooted frame

with

3 points is

if its root cluster

simple

F

and at least one of the final clusters are simple. Suppose

⊆

W" R

is a

F

9

simple frame. a

" a

" . . . " a

" a

" . . . " a

are all its points. with a

being

.

.

".

.

m

m

n

h

i

the root. C (a

)" . . . " C (a

) all the distinct immediate cluster-successors of

.

m

'
5—ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

a

. and a

a final point with simple C (a

). For every k ⊆ 1" . . . " n. define a

.

n

n

formula :

by taking

k

n

:

⊆

k

.

ij

.

i

.

.

p

k

a

Ra

:i

i

.

j

5.

i

5.

.

.

.

.

1

where .

. .

were defined in Section 2.3 and .

⊆

(

ij

i

.

p

i

).

1

. :

i

5.

Now we associate with

the formula ( (

) ⊆

p

:

if m ⊆ 1. and the

F

F

.

.

n

.

.

.

.

V

,

formula ( (

) ⊆

:

. . .

:

if m " 1.

.

m

F

.

.

,

,

LEMMA 2.20

For every simple frame

.

( (

)

—(

"

)

:

F

F

F

S,

?

"

:

Proof

G

F

G

F

It is enough to show that

⊆ ( (

) implies

⊆ —(

"

). for any

finite

. So suppose ( (

) is refuted in a finite frame

under some valuation.

G

F

G

'j

'j

:

Define a partial map f from

onto

by taking

G

F

a

if x

⊆ ( (

)

.

F

'j

f (x) ⊆

1

a

i

if x

⊆ :

. 1

i

n

i

undefined otherwise.

'j

7

7

9

8

One can readily check that f is a subreduction of

to

. However it is not

G

F

necessarily cofinal. So we extend f by putting f (x) ⊆ a

. for every x of

n

depth 1 in

such that f (x

) ⊆

a

. Clearly. the improved map is still a

.

G

subreduction of

to

. and .

ensures its cofinality.

G

F

.

;

f

g

.

1

Using the semantical properties of the canonical formulas it is a matter

of routine to prove the following

LEMMA 2.21

i

1" . . . " m

Suppose

and

is the subframe of

generated

G

F

by

: Then

a

i

—(

"

)

:

:

i

G

S,

? f

g

:

?

"

We are in a position now to prove a criterion of DP for the cofinal sub-

frame logics in NExt

.

S,

THEOREM 2.23

L

NExt

A consistent co.nal subframe logic

has the

S,

disjunction property i, no frame

in its independent axiomatization ?86"

i

F

?

is simple. for

i

I

:

?

Proof

F

(

) Suppose. on the contrary. that

is simple. for some i

I .

i

Since the axiomatization (16) is independent. every proper generated sub-

8

?

frame of

validates L. By Lemma 2.20. ( (

)

L and so either p

L or

i

i

.

F

F

:

L. However. both alternatives are impossible: the former means that

?

?

j

?

L is inconsistent. while the latter. by Lemma 2.21. implies —(

"

)

L.

G

where

is the subframe of

generated by an immediate successor of

's

i

i

G

F

F

:

?

root.

"
ADVANCED MODAL LOGIC

5——

A

.

A

.

G

G

.

,

A

.

A

.

A

.

A

.

A

.

A

.

y

o

o

o

'I

"(

"

'

"

'

"

o

x

Figure 17.

(

) Given two finite rooted frames

and

for L. we construct the

.

,

G

G

⊆

frame

as shown in Fig. 17 and prove that

⊆ L. Suppose otherwise. i.e.

F

F

there exists a cofinal subreduction f of

to

. for some i

I . Let x

be the

i

i

F

F

j

root of

. Since

and

are not cofinally subreducible to

and since

i

i

.

,

F

G

G

F

?

L is consistent. f

(x

) ⊆

x

. By the cofinality condition. it follows in

5

i

.

particular that y

domf . But then

is simple. which is a contradiction.

i

f

g

F

Thus. by Theorem 2.36. L has DP.

.

?

Note that in fact the proof of (

) shows that if L

NExt

.

is

S,

F

a simple frame. —(

"

)

L and —(

"

)

L for any proper generated

F

G

8

?

subframe

of

then L does not have DP. Transferring this observation to

G

F

:

?

:

'?

the intuitionistic case. we obtain

THEOREM 2.22 (Minari 1966. Zakharyaschev 1968)

If a siffilogic is consis5

tent and has DP then the disjunction free fragments of

and

are the

L

Int

same:

Sufficient conditions of DP in terms of canonical formulas can be found

in [Chagrov and Zakharyaschev 1992. 1998].

Since classical logic is not constructive. it is of interest to find maximal

consistent si-logics with DP. That they exist follows from Zorn's Lemma.

Here is a concrete example of such a logic.

Trying to formalize the proof interpretation of intuitionistic logic. Med-

vedev (1963) proposed to treat intuitionistic formulas as finite problems.

Formally. a

is a pair

X" Y

of finite sets such that Y

X

.nite problem

and X

⊆

4 elements in X are called

and elements in Y

possible solutions

h

i

ff

solutions

to the problem. The operations on finite problems. corresponding

fl

to the logical connectives. are defined as follows:

X

" Y

X

" Y

⊆

X

X

" Y

Y

"

.

.

,

,

.

,

.

,

h

i . h

i

h

’

’

i

X

" Y

X

" Y

⊆

X

X

" Y

Y

"

.

.

,

,

.

,

.

,

h

i , h

i

h

t

t

i

'
5—(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

5o

5o

5o

5

5

5

5

5

5

"(

'I

'I

"(

'I

"(

o

o

o

o

5

5

5

"

"

"

"

'

5

5

'

5

"

'

"

o

o

o

o

o

o

'I

"(

'I

"(

'I

"(

'I

"(

o

'I

o

"(

o

5

5

5

"

"

"

"

"

5

5

5

5

5

5

"

5

5

'

5

"

'

"

'

5o

5o

5o

5

5

5

5

5

5

'

"

'

"

'

"

'

5

"

5

'

5

"

"

'

"

'

"

5

'

"

5

'

5

'

"

5

5

5

5

5

5

5o

5

5

o

o

o

o

o

o

o

o

o

'I

"(

'I

"(

'I

"(

5

'

"

'

"

'

"

5

"

"

'

"

'

"

'

"

5

5

5

o

o

o

o

Figure 16.

X

" Y

X

" Y

⊆

X

"

f

X

: f (Y

)

Y

"

.

.

,

,

.

,

,

,

h

i . h

i

f

?

ff

g

D

E

X

X

.

.

⊆

X"

.

:

h

fli

Y

Here X

Y ⊆ (X

1

)

(Y

3

) and X

is the set of all functions from

X into Y . Note that in the definition of

the set X is fixed. but arbitrary4

t

’ f

g

6

’ f

g

for definiteness one can take X ⊆

.

:

fflg

Now we can interpret formulas by finite problems. Namely. given a for-

mula . we replace its variables by arbitrary finite problems and perform

the operations corresponding to the connectives in .

If the result is a

problem with a non-empty set of solutions no matter what finite problems

are substituted for the variables in . then . is called

.nitely valid

. One

can show that the set of all finitely valid formulas is a si-logic4 it is called

Medvedev1s logic

and denoted by

.

ML

In fact.

can be defined semantically. Medvedev (1966) showed that

ML

ML

coincides with the set of formulas that are valid in all frames

having

n

B

the form of the n-ary Boolean cubes with the topmost point deleted4 for

n ⊆ 1" 3" 2" 5. the Medvedev frames are shown in Fig. 16. Since

"

is

n

m

B

B

a generated subframe of

.

has DP. Moreover. Levin [1969] proved

n

m

"

B

ML

that it has no proper consistent extension with DP. The following proof of

this result is due to Maksimova [1966].

THEOREM 2.25 (Levin 1969)

is a maximal siffilogic with DP:

ML

Proof

Suppose. on the contrary. that there exists a proper consistent ex-

tension L of

having DP. Then we have a formula .

L

. We

ML

ML

show first that there is an essentially negative substitution instance .

of

.

?

[

. such that .

. Since .(p

" . . . " p

)

. there is a Medvedev

ML

ML

.

.

n

frame

refuting . under some valuation

. With every point x in

m

m

B

V

B

'?

'?

we associate a new variable q

and extend

to these variables by taking

x

V

V

B

(q

) to be the set of final points in

that are not accessible from x. By

x

m

ADVANCED MODAL LOGIC

5—)

the construction of

. we have y

⊆

q

iff y

x

. from which

m

x

B

j

-

?

3

V

V

(

q

) ⊆

(p

).

x

i

-

x

"

p

V

1

9

i

:

Let .

⊆ .(

q

" . . . "

q

). It follows that

(.

) ⊆

(.)

.

x

x

.

V

V

x

p

x

p

V

V

1

9

.

1

9

n

:

-

:

-

and so .

.

ML

.

W

W

'?

Thus. we may assume that . is an essentially negative formula. Since

KP

ML

ML

.

contains the formulas

ff

nd

k

k

k

⊆ (

p

q

. . .

q

)

(

p

q

)

. . .

(

p

q

)

.

.

-

. -

,

, -

.

-

. -

,

,

-

. -

which. as is easy to see. belong to

. Let us consider the logic

KP

ND

Int

nd

⊆

"

: k

1

.

k

f

9

g

Using the fact that the outermost

in

can be replaced with

and that

k

nd

(

p

q)

(

p

q)

. one can readily show that every essentially

Int

.

5

-

. -

5 -

-

.

?

negative formula is equivalent in

to the conjunction of formulas of the

ND

form

?

. . .

?

. So L

contains a formula of the form

?

. . .

?

.

.

l

.

l

ML

-

,

,-

[

-

,

,-

Since L has DP.

?

L for some i. But then. by Glivenko's Theorem.

i

?

i

ML

. which is a contradiction.

.

-

?

-

?

Remark. ML

is not finitely axiomatizable. as was shown by Maksimova

et al:

[1989]. Nobody knows whether it is decidable.

It turns out. however. that

is not the unique maximal logic with DP

ML

in Ext

. Kirk [1963] noted that there is no greatest consistent si-logic

Int

with DP. Maksimova [1965] showed that there are infinitely many maximal

constructive si-logics. and Chagrov [1993a] proved that in fact there are

a continuum of them4 see also Ferrari and Miglioli [1992. 1997a. 1997b].

Galanter [1990] claims that each si-logic characterized by the class of frames

of the form

W : W

1" . . . " n

" W

⊆

"

W

N

"

"

hf

ff f

g

fl

j

j '?

g

(i

where n ⊆ 1" 3" . . . and N is some fixed infinite set of natural numbers. is a

maximal si-logic with DP.

:,' Intuitionistic Modal Logics

All modal logics we have dealt with so far were constructed on the classical

non-modal basis. It can be replaced by logics of other types. For instance.

one can consider modal logics based on relevant logic (see e.g. [Fuhrmann

1969]) or many-valued logics (see e.g.

[Segerberg 1968]. [Morikawa 1969].

'
5—0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

[Ostermann 1966]). and many others.

In this section we briefly discuss

modal logics with the intuitionistic basis.

Unlike the classical case. the intuitionistic

and

are not supposed to

.

,

be dual. which provides more possibilities for defining intuitionistic modal

logics. For a non-empty set

of modal operators. let

be the stan-

M

M

dard propositional language augmented by the connectives in

. By an

M

L

intuitionistic modal logic

in the language

we understand any subset of

M

M

Int

containing

and closed under modus ponens. substitution and the

L

L

regularity rule .

:,

.

: . for every

.

M

There are three ways of defining intuitionistic analogues of (classical)

.

#

. #

# ?

normal modal logics. First. one can take the family of logics extending the

basic system

in the language

which is axiomatized by adding to

IntK

.

.

Int

K

the standard axioms of

L

.

.

.

.

(p

q)

p

q and

.

.

5

.

]

An example of a logic in this family is Kuznetsov's [1967] intuitionistic

provability logic

(Kuznetsov used

instead of

). the intuitionistic

(

I

.

analog of the provability logic

. It can be obtained by adding to

GL

IntK

.

)

(and even to

) the axioms

Int

p

p" (

p

p)

p" ((p

q)

p)

(

q

p).

.

.

.

.

.

.

.

.

.

.

A model theory for logics in NExt

was developed by Ono [1988].

IntK

.

Bo)zioc and Do)sen [1965]. Do)sen [1967a]. Sotirov [1965] and Wolter and Za-

kharyaschev [1998a.b]4 we discuss it below. Font [1965. 1966] considered

these logics from the algebraic point of view. and Luppi [1996] investigated

their interpolation property by proving. in particular. that the superamal-

gamability of the corresponding varieties of algebras is equivalent to inter-

polation.

A possibility operator

in logics of this sort can be defined in the classical

,

way by taking

. ⊆

. Note. however. that in general this

does not

,

.

,

distribute over disjunction and that the connection via negation between

.

-

-

and

is too strong from the intuitionistic standpoint (actually. the situation

,

here is similar to that in intuitionistic predicate logic where

and

are not

dual.)

1

)

Another family of "normal" intuitionistic modal logics can be defined in

the language

by taking as the basic system the smallest logic in

to

,

,

contain the axioms

L

L

,

,

,

,

(p

q)

p

q and

4

,

5

,

-

:

it will be denoted by

. Logics in NExt

were studied by Bo)zioc

IntK

IntK

,

,

and Do)sen [1965]. Do)sen [1967a]. Sotirov [1965] and Wolter [1998c].

ADVANCED MODAL LOGIC

5—?

Finally. we can define intuitionistic modal logics with independent

and

.

,

. These are extensions of

. the smallest logic in the language

IntK

.,

.,

containing both

and

. Fischer Servi [1960. 1965] constructed a

IntK

IntK

.

,

L

logic in NExt

by imposing a weak connection between the necessity

IntK

.,

and possibility operators:

FS

IntK

.,

⊆

(p

q)

(

p

q)

(

p

q)

(p

q).

,

.

,

,

.

.

"

.

.

.

"

.

.

.

A remarkable feature of

is that the standard translation S T of modal

FS

formulas into first order ones (see

) not only embeds

Correspondence Theory

K

FS

into classical predicate logic but also

into intuitionistic first order

logic: . belongs to the former iff S T (.) is a theorem of the latter. According

to Simpson [1995]. this result was proved by C. Stirling4 see also Grefe [1998].

Various extensions of

were studied by Bull [1966a]. Ono [1988]. Fischer

FS

Servi [1988. 1960. 1965]. Amati and Pirri [1995]. Ewald [1966]. Wolter and

Zakharyaschev [1998b]. Wolter [1998c]. The best known one is probably the

logic

MIPC

FS

⊆

p

p

p

p

p

p

.

.

.

,

.,

"

.

"

.

"

.

"

p

p

p

p

p

p

,

,,

,

,.

.

.

"

.

"

.

introduced by Prior [1978]. Bull [1966a] noticed that the translation

de-

.

fined by

(p

)

⊆ P

(x).

⊆

.

i

.

i

.

:

:

(:

?)

⊆ :

?

. for

"

"

.

.

.

.

$

$

$ ? f.

,

.g

.

,

(

:)

⊆

x :

. (

:)

⊆

x :

.

.

.

.

)

1

is an embedding of

into the monadic fragment of intuitionistic pred-

MIPC

icate logic. Ono [1988]. Ono and Suzuki [1966]. Suzuki [1990]. and Bezhan-

ishvili [1998] investigated the relations between logics in NExt

and

MIPC

superintuitionistic predicate logics induced by that translation.

In what follows we restrict attention only to the classes of intuitionistic

modal logics introduced above. An interesting example of a system not

covered here was constructed by Wijesekera [1990]. A general model theory

for such logics is developed by Sotirov [1965] and Wolter and Zakharyaschev

[1998b].

Let us consider first the algebraic and relational semantics for the logics

introduced above. All the semantical concepts to be defined below turn

out to be natural combinations of the corresponding notions developed for

classical modal and si-logics. For details and proofs we refer the reader to

Wolter and Zakharyaschev [1998a.b].

From the algebraic point of view. every logic L

NExt

. for

IntK

M

M

.

,

"

. corresponds to the variety of Heyting algebras with one or two

?

ff

f

g

5—fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

operators validating L. The variety of algebras for

will be called the

IntK

M

variety of

5algebras

.

M

To construct the relational representations of

-algebras. we define a

-

M

.

frame

to be a structure of the form

W" R" R

" P

in which

W" R" P

is an

.

intuitionistic frame. R

a binary relation on W such that

.

h

i

h

i

and P is closed under the operation

R

R

R ⊆ R

.

.

o

o

.

.

X ⊆

x

W :

y

W (xR

y

y

X )

.

f

?

)

?

.

?

g

A

-

has the form

W" R" R

" P

. where

W" R" P

is again an intu-

frame

,

,

itionistic frame. R

a binary relation on W satisfying the condition

,

h

i

h

i

.

.

R5

R

R5

⊆ R

,

,

o

o

and P is closed under

,

,

X ⊆

x

W :

y

X xR

y

.

f

?

1

?

g

Finally. a

-

is a structure

W" R" R

" R

" P

the unimodal reducts

frame

.,

.

,

W" R" R

" P

and

W" R" R

" P

of which are

- and

-frames. respec-

.

,

.

,

h

i

h

i

h

i

tively. (To see why the intuitionistic and modal accessibility relations are

connected by the conditions above the reader can construct in the standard

way the canonical models for the logics under consideration. The important

point here is that we take the Leibnizean definition of the truth-relation for

the modal operators. Other definitions may impose different connecting

conditions4 see below.)

Given a

-frame

⊆

W" R" R

" R

" P

. it is easy to check that its

dual

.,

F

.

,

h

i

"

F

⊆

P"

"

"

"

"

"

.

,

h

0

6

.

fl

i

is a

-algebra. Conversely. for each

-algebra

⊆

A"

"

"

"

"

"

A

.,

.,

.

,

we can define the

dual frame

h

.

,

.

:

i

A

"

⊆

W" R" R

" R

" P

.

,

h

i

by taking

W" R" P

to be the dual of the Heyting algebra

A"

"

"

"

and putting

h

i

h

.

,

.

:i

.

,

.

,

R

iff

a

A (

a

a

)"

.

.

r

r

)

?

? r

.

? r

.

,

,

.

R

iff

a

A (a

a

).

,

,

r

r

)

?

? r

.

? r

A

A

A

.,

"

⊆

"

is a

-frame and. moreover.

(

)

. Using the standard technique

"

2

of the model theory for classical modal and si-logics. one can show that a

ADVANCED MODAL LOGIC

5—'

.,

F

F

F

.

,

-frame

is isomorphic to its bidual (

)

iff

⊆

W" R" R

" R

" P

is

"

"

descriptive

. i.e.

W" R" P

is a descriptive intuitionistic frame and. for all

h

i

x" y

W .

?

h

i

xR

y iff

X

P (x

X

y

X )"

.

.

)

?

?

.

?

xR

y iff

X

P (y

X

x

X ).

,

,

)

?

?

.

?

Thus we get the following completeness theorem.

THEOREM 2.27

L

NExt

Every logic

is characterized by a suit5

IntK

.,

able class of ?descriptive"

5frames. e:g: by the class

:

⊆ L

:

"

A

A

.,

?

f

j

g

Similar results hold for logics in NExt

and NExt

.

IntK

IntK

.

,

As usual. by a

we understand a frame

W" R" R

" R

" P

Kripke frame

.

,

in which P consists of all R-cones4 in this case we omit P . An intuition-

h

i

istic modal logic L is

-

if the underlying Kripke frame of each

persistent

descriptive frame for L validates L. For example.

as well as the logics

FS

D

L

IntK

.,

,

.

.

,

(k " l" m" n) ⊆

p

p"

for k " l" m" n

0

k

l

m

n

"

.

9

are

-persistent and so Kripke complete (see Wolter and Zakharyaschev

D

[1998b]). Descriptive frames validating

satisfy the conditions

FS

xR

y

z (yRz

xR

z

xR

z )"

,

.

,

. 1

.

.

xR

y

z (xRz

zR

y

zR

y)"

.

.

,

. 1

.

.

and those for

(k " l" m" n) satisfy

L

k

m

l

n

xR

y

xR

y

u (yR

u

zR

u).

,

.

.

,

.

. 1

.

It follows. in particular. that

is

-persistent4 its Kripke frames have

MIPC

the properties: R

is a quasi-order. R

⊆ R

and R

⊆ R

(R

R

). On

.

5

.

,

.

.

,

D

.

the contrary.

is not

-persistent. although it is complete with respect to

(

I

o

0

the class of Kripke frames

W" R" R

such that

W" R

is a frame for

.

.

GL

D

and R the reflexive closure of R

.

.

h

i

h

i

The next step in constructing duality theory of

-algebras and

-frames

M

M

is to find relational counterparts of the algebraic operations of forming ho-

momorphisms. subalgebras and direct products. Let

⊆

W" R" R

" R

" P

F

.

,

be a

-frame and V a non-empty subset of W such that

.,

h

i

x

V

y

W (xR

y

xRy

y

V )"

.

)

?

)

?

,

.

?

x

V

y

W (xR

y

z

V (xR

z

yRz )).

,

,

)

?

)

?

. 1

?

.

Then

⊆

V " R

V " R

V " R

V "

X

V : X

P

is also a

-frame

G

.

,

.

.

.

.,

which is called the

V . The former of the two

subframe of

generated by

F

h

f

0

?

gi

5([

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

y

z

z

R

.

o

AK

.—

o

o

"

R

A

.

R

.

.

R

.

A

.

F

G

x

x

o

o

Figure 18.

0

1

5

01

5

R

.

S

.

0

0

o

"

o

AK

.—

o

o

o

'I

"

"

"

S

.

R

R

A

.

R

S

'

S

.

A

.

'

"

S

.

"8

0

S

.

o

o

o

o

3

2

3

2

F

G

Figure 16.

conditions above is standard: it requires V to be upward closed with respect

to both R and R

. However. the latter one does not imply that V is upward

.

closed with respect to R

: the frame

in Fig. 18 is a generated subframe

,

G

of

. although the set

x" z

is not an R

-cone in

. This is one difference

F

,

F

from the standard (classical modal or intuitionistic) case. Another one arises

f

g

when we define the relational analog of subalgebras.

Given

-frames

⊆

W" R" R

" R

" P

and

⊆

V " S" S

" S

" Q

. we

.,

F

G

.

,

.

,

say a map f from W onto V is a

reduction

of

to

if f

(X )

P for

5

F

G

h

i

h

i

.

?

every X

Q and. for all x" y

W and u

V .

?

?

?

xRy implies f (x)S f (y).

xR

y implies f (x)S

f (y). for

"

.

.

,

)

)

# ? f

g

.

f (x)S u implies

z

f

(u) xRz .

5

f (x)S

u implies

z

f

(u) xR

z .

5

.

.

1

?

.

1

?

f (x)S

u implies

z

W (xR

z

uS f (z )).

,

,

1

?

.

Again. the last condition differs from the standard one: given f (x)S

f (y).

,

in general we do not have a point z such that xR

z and f (y) ⊆ f (z ). witness

,

the map gluing 0 and 1 in the frame

in Fig. 16 and reducing it to

.

F

G

Note that both these concepts coincide with the standard ones in classical

modal frames. where R and S are the diagonals. The relational counterpart

of direct products—disjoint unions of frames—is defined as usual.

THEOREM 2.26 (i)

V

If

is the subframe of a

5frame

generated by

G

F

.,

then the map

de.ned by

h

h(X ) ⊆ X

V

X

. for

an element in

. is a

"

F

0

ADVANCED MODAL LOGIC

5(5

homomorphism from

onto

:

F

G

"

"

(ii)

h

If

is a homomorphism from a

5algebra

onto a

5algebra

.,

.,

A

B

then the map

de.ned by

h

h

(

) ⊆ h

(

)

.

a prime .lter in

. is an

"

"

5

B

.

isomorphism from

onto a generated subframe of

:

B

A

"

"

r

r

r

(iii)

f

If

is a reduction of a

5frame

to a

5frame

then the map

.,

.,

F

G

"

"

.

"

f

f

(X ) ⊆ f

(X )

X

de.ned by

.

an element in

. is an embedding of

5

G

"

"

G

F

into

:

(iv)

f

If

is a subalgebra of a

5algebra

then the map

de.ned by

B

A

.,

f (

) ⊆

B

.

a prime .lter in

and

the universe of

. is a reduction

B

A

B

r

r 0

r

of

to

:

A

B

"

"

This duality can be used for proving various results on modal definability.

For instance. a class

of

-frames is of the form

⊆

:

⊆ Φ

. for some

.,

F

F

set Φ of

-formulas. iff

is closed under the formation of generated sub-

.,

C

C

f

j

g

frames. reducts. disjoint unions. and both

and its complement are closed

L

C

under the operation

(

)

(see Wolter and Zakharyaschev [1998b]).

"

F

F

"

C

Moreover. one can extend Fine's Theorem connecting the first order defin-

".

ability and

-persistence of classical modal logics to the intuitionistic modal

case:

D

THEOREM 2.28

L

NExt

If a logic

is characterized by an ele5

IntK

.,

mentary class of Kripke frames then

is

5persistent:

L

?

D

These results may be regarded as a justification for the relational seman-

tics introduced in this section. However. it is not the only possible one. For

example. Bo)zioc and Do)sen [1965] impose a weaker condition on the con-

nection between R and R

in

-frames. Fisher Servi [1960] interprets

FS

.

.

in birelational Kripke frames of the form

W" R" S

in which R is a partial

order. R

S

S

R. and

o

ff

o

h

i

xRy

xS z

u (yS u

zRu).

.

. 1

.

The intuitionistic connectives are interpreted by R and the truth-conditions

for

and

are defined as follows

.

,

.

X ⊆

x

W :

y " z (xRyS z

z

X

"

f

?

)

.

?

g

,

X ⊆

x

W :

y

X xS y

.

f

?

1

?

g

In birelational frames for

S is an equivalence relation and

MIPC

xS yRz

u xRuS z .

. 1

These frames were independently introduced by L. Esakia who also estab-

lished duality between them and "monadic Heyting algebras".

5(ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

There are two ways of investigating various properties of intuitionistic

modal logics. One is to continue extending the classical methods to logics

in NExt

. Another one uses those methods indirectly via embeddings

IntK

M

of intuitionistic modal logics into classical ones. That such embeddings

are possible was noticed by Shehtman [1989]. Fischer Servi [1960. 1965].

and Sotirov [1965]. Our exposition here follows Wolter and Zakharyaschev

[1998a.b]. For simplicity we confine ourselves only to considering the class

NExt

and refer the reader to the cited papers for information about

IntK

.

more general embeddings.

Let T be the translation of

into

prefixing

to every subfor-

I

I

.

.

.

.

mula of a given

-formula. Thus. we are trying to embed intuitionistic

.

L

L

modal logics in NExt

into classical bimodal logics with the necessity

L

IntK

.

operators

(of

) and

. Say that T

L

NExt

into

embeds

I

.

.

S,

IntK

.

M

NExt(

) (

in

and

in

) if. for every .

.

S,

K

S,

K

.

.

.

I

?

?

&

L

L

? L

.

L iff T (.)

M .

?

?

In this case M is called a

(or BM-)

of L.

bimodal

companion

For every logic M

NExt(

) put

S,

K

?

&

,

.

M ⊆

.

: T (.)

M

"

f

? L

?

g

and let

be the map from NExt

into NExt(

) defined by

.

IntK

S,

K

.

&

.

IntK

Grz

K

mix

(

Φ) ⊆ (

)

T (Φ)"

.

"

&

"

"

where Φ

and

⊆

p

p. (The axiom

reflects the

I

I

mix

mix

.

.

.

.

condition R

R

R ⊆ R

of

-frames.) Then we have the following

ff L

5

.

.

.

extension of the embedding results of Maksimova and Rybakov [1985]. Blok

o

o

[1986] and Esakia [1989a.b]:

THEOREM 2.26 (i)

The map

is a lattice homomorphism from the lattice

,

NExt(

)

NExt

onto

preserving decidability. Kripke complete5

S,

K

IntK

.

ness. tabularity and the .nite model property:

&

(ii)

Φ

T

M

Each logic

is embedded by

into any logic

in the

IntK

.

interval

"

(

)

T (Φ)

M

(

)

T (Φ).

S,

K

Grz

K

mix

&

"

ff

ff

&

"

"

(iii)

NExt

The map

is an isomorphism from the lattice

onto the

.

IntK

.

lattice

NExt(

)

preserving FMP and tabularity:

Grz

K

mix

&

"

Note that Fischer Servi [1960] used another generalization of the G;odel

translation. She defined

,

,

T (

.) ⊆

T (.)"

ADVANCED MODAL LOGIC

5(—

and showed that this translation embeds

into the logic

FS

.

.

.

T (

.) ⊆

T (.)

I

S,

K

(

)

p

p

I

I

I

p

I

p.

,.

.

,

,,

,

,

&

"

.

"

.

It is not clear. however. whether all extensions of

can be embedded into

FS

classical bimodal logics via this translation.

Let us turn now to completeness theory of intuitionistic modal logics. As

to the standard systems

.

. and

. their FMP can be proved

I

FS

MIPC

(

by using (sometimes rather involved) filtration arguments4 see Muravit-

skij [1961]. Simpson [1995] and Grefe [1998]. and Ono [1988]. respectively.

Further results based on the filtration method were obtained by Sotirov

[1965] and Ono [1988]. However. in contrast to classical modal logic. only a

few general completeness results covering interesting classes of intuitionistic

modal logics are known. The proofs of the following two theorems are based

on the translation into classical bimodal logics discussed above.

THEOREM 2.29

" Φ

Suppose that a siffilogic

has one of the properties"

Int

decidability. Kripke completeness. FMP: Then the logics

Φ

and

IntK

.

IntK

.

.

Φ

p

p

also have the same property:

"

"

"

.

Proof

It suffices to show that there is a BM-companion of each of these

systems satisfying the corresponding property. Notice that

,

S,

K

IntK

((

T (Φ))

) ⊆

Φ"

.

"

&

"

,

S,

K

IntK

((

T (Φ))

(

p

p)) ⊆

Φ

p

p.

.

.

.

"

&

"

.

"

"

.

So it remains to use the fact that if

" Φ has one of the properties

Int

under consideration then its smallest modal companion

T (Φ) has this

S,

property as well (Table 8). and if L

. L

are unimodal logics having one

.

,

"

of those properties then the fusion L

L

also enjoys the same property

.

,

&

(Theorem 3.6).

.

Such a simple reduction to known results in classical modal logic is not

available for logics containing

⊆

p

p. However.

IntK,

IntK

.

.

.

.

by extending Fine's [1985] method of maximal points to bimodal compan-

"

.

ions of extensions of

Wolter and Zakharyaschev [1998a] proved the

IntK,

.

following:

THEOREM 2.50

L

Suppose

has a

5persistent BMfficompanion

IntK,

.

M

(

)

S,

K,

mix

whose Kripke frames are closed under the formation

(

D

(

&

"

of substructures: Then

(i)

Φ

for every set

of intuitionistic negation and disjunction free formulas.

L

Φ

has FMP'

"

5((

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

(ii)

Φ

for every set

of intuitionistic disjunction free formulas and every

n

1

.

9

n

L

Φ

(p

p

)

i

j

"

"

.

i

5.

"

j

i

"

5

has the .nite model property:

One can use this result to show that the following (and many other)

intuitionistic modal logics enjoy FMP:

(1)

4

IntK,

.

(3)

⊆

p

p (R

is reflexive)4

IntS,

IntK,

.

.

.

.

(2)

.

⊆

(

p

q)

(

q

p) (R

is reflexive and

IntS,

5

IntS,

.

.

.

.

.

.

.

"

.

connected)4

"

.

,

.

(5)

p

p (R

is symmetrical)4

IntK,

.

.

.

.

(7)

p

p (R

is Euclidean)4

IntK,

.

.

.

.

.

"

,

-

(6)

p

p (xRy

xR

z

yR

z )4

IntK,

.

.

.

.

.

"

,

-

"

, -

.

.

We conclude this section with some remarks on lattices of intuitionis-

tic modal logics. Wolter [1998c] uses duality theory to study splittings of

lattices of intuitionistic modal logics. For example. he showed that each

finite rooted frame splits NExt(L

p

p). for L ⊆

and

,

IntK

.

n

n

".

.

.

L ⊆

. and each R

-cycle free finite rooted frame splits the lattices of

FS

.

"

.

extensions of

and

. No positive results are known. however. for

IntK

FS

.

the lattice NExt

. In fact. the behavior of

-frames is quite different

IntK

,

,

from that of frames for

. For instance. in classical modal logic we have

FS

RG

GR

G

R

⊆

. for each class of frames (or even

-frames)

. where

and

.

F

F

F

are the operations of forming generated subframes and reducts. respectively.

But this does not hold for

-frames. More precisely. there exists a finite

,

,

G

G

G

RG

GR

-frame

such that

. In other terms. the variety of modal

algebras for

has the

(i.e. each congruence

congruence extension property

K

f

g '(

f

g

of a subalgebra of a modal algebra can be extended to a congruence of the

algebra itself ) but this is not the case for the variety of

-algebras.

,

Vakarelov [1961. 1967] and Wolter [1998c] investigate how logics having

Int

as their non-modal fragment are located in the lattices of intuitionistic

modal logics. It turns out. for instance. that in NExt

the inconsistent

IntK

,

logic has a continuum of immediate predecessors all of which have

as

Int

their non-modal fragment. but no such logic exists in the lattice of extensions

of

.

IntK

.

5 ALGORITHMIC PROBLEMS

All algorithmic results considered in the previous sections were positive:

we presented concrete procedures for deciding whether an arbitrary given

"
ADVANCED MODAL LOGIC

5()

formula belongs to a given logic in some class or whether it axiomatizes

a logic with a certain property. What is the complexity of those decision

algorithms? Do there exist undecidable calculi

and properties? These are

.-

the main questions we address in this chapter.

",. Undecidable calculi

The first undecidable modal and si-calculi were constructed by Thomason

[1987c] (polymodal and unimodal). Isard [1988] (unimodal) and Shehtman

[1986b] (superintuitionistic). However. we begin with the very simple exam-

ple of [Shehtman 1963] which is a modal reformulation of the undecidable

associative calculus T of [Tseitin 1976]. The axioms of T are

ac ⊆ ca"

ad ⊆ da"

bc ⊆ cb"

bd ⊆ db"

edb ⊆ be"

eca ⊆ ae"

abac ⊆ abacc.

The reader will notice immediately an analogy between them and the axioms

of the following modal calculus with five necessity operators:

L ⊆

p

p

p

p

K

"

.

:

:

.

.

'

'

.

.

.

.

.

.

.

.

.

"

5

"

5

"

.

.

.

.

.

.

.

.

,

:

:

,

,

'

'

,

p

p

p

p

5

"

5

"

.

.

.

.

.

.

.

.

.

.

"

'

,

,

"

"

:

.

.

"

p

p

p

p

5

"

5

"

.

.

.

.

.

.

.

.

.

.

,

.

:

.

,

.

:

:

p

p.

5

Moreover. it is not hard to see that words x. y in the alphabet

a" b" c" d" e

are equivalent in T

iff f (x)p

f (y)p

. where f is the natural

K

"

.—

f

g

one-to-one correspondence between such words and modalities in language

5

?

.

.

.

.

.

.

.

.

.

"

:

.

'

"

'

,

" . . . "

under which. for instance. f (cadedb) ⊆

. It

f

g

follows immediately that L is undecidable. Using the undecidable associa-

tive calculus of Matiyasevich [1968]. one can construct in the same way an

undecidable bimodal calculus having three reductions of modalities as its

axioms. It is unknown whether there is an undecidable unimodal calculus

axiomatizable by reductions of modalities.

Thomason's simulation and the undecidable polymodal calculi mentioned

above provide us with examples of undecidable calculi in NExt

. However.

K

to find axioms of undecidable unimodal calculi with transitive frames. as

well as undecidable si-calculi. a more sophisticated construction is required.

.?

By a calculus we mean a logic with :nitely many axioms ]inference rules in our case

are :xed78

."

I8e8- they can be obtained from each other by a :nite number of transformations of

the form

- where

5

or

5

is an axiom of

8

w

ww

w

vw

w

v

v

w

T

5

.

,

.

,

5(0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

b

d

X

Xy

5

"

Xy

X

X

X

d

.

.—

5

X

X

Xy

Xy

X

X

d

,

o

a

X

X

X

X

.

.—

5

Xy

X

g

.

X

X

5

'I

g

.

.

.—

5

Xy

X

g

,

'

.

X

X

.

.

.

5

'I

a

.

5

5

.

.

"

'I

'

.

a

.

5

.

"

'

,

a

.

5

"

.

.

,

a

a

a

.

.

.

5

5

5

"

"

"

.

.

,

a

a

a

,

,

,

.

.

.

5

.

5

.

5

.

.

.

.

.

.

,

a

a

a

t

.

k

l

.

.

5

5

5

5

5

5

"

"

"

.

.

,

a

a

a

t

k

16

l

.

.

.

5

J6

24

5

.

.

5

.

1

.

.

.

1

J

2

1

1

J

1
2

. . .

. . .

5

e(t" k " l)

Figure 19.

Instead of associative calculi. let us use now Minsky machines with two

tapes (or register machines with two registers). A

is a

Minsky machine

finite set (program) of instructions for transforming triples

s" m" n

of nat-

ural numbers. called

. The intended meaning of the current

con.gurations

h

i

configuration

s" m" n

is as follows: s is the number (label) of the current

machine state and m. n represent the current state of information. Each

h

i

instruction has one of the four possible forms:

s

t" 1" 0

" s

t" 0" 1

"

. h

i

. h

i

s

t"

1" 0

(

t. " 0" 0

)" s

t" 0"

1

(

t. " 0" 0

).

. h

[

i

h

i

. h

[

i

h

i

The last of them. for instance. means: transform

s" m" n

into

t" m" n

1

if n " 0 and into

t

" m" n

if n ⊆ 0. For a Minsky machine

. we shall

.

P

h

i

h

[

i

write

:

s" m" n

t" k " l

if starting with

s" m" n

and applying the

P

h

i

instructions in

. in finitely many steps (possibly. in 0 steps) we can reach

P

h

i . h

i

h

i

t" k " l

.

h

i

We shall use the well known fact (see e.g.

[Mal'cev 1980]) that the fol-

lowing

is undecidable: given a program

and con-

con.guration problem

P

,gurations

s" m" n

.

t" k " l

. determine whether

:

s" m" n

t" k " l

.

P

With every program

and configuration

s" m" n

we associate the transi-

P

h

i

h

i

h

i . h

i

tive frame

depicted in Fig. 19. Its points e(t" k " l) represent configurations

F

h

i

t" k " l

such that

:

s" m" n

t" k " l

4 e(t" k " l) sees the points a

. a

. a

P

t

k

l

.

.

,

h

i

h

i . h

i

ADVANCED MODAL LOGIC

5(?

representing the components of

t" k " l

. The following variable free formulas

characterize points in

in the sense that each of these formulas. denoted by

F

h

i

Greek letters with subscripts and*or superscripts. is true in

only at the

F

point denoted by the corresponding Roman letter with the same subscript

and*or superscript:

— ⊆

" ] ⊆

" ( ⊆

—

]

] "

,

.,

.

,

,

,

,

] .

]

:

.

. -

9 ⊆

(

]

] " 9

⊆

9

9" 9

⊆

9

9

"

.

,

.

.

,

,

,

,

,

,

,

,

,

-

.

. -

. -

. -

(

⊆

(

(

9" (

⊆

(

(

9"

.

,

.

.

,

,

,

,

,

,

,

,

. -

. -

. -

. -

.

,

,

—

⊆

(

9

(

9"

.

,

,

,

,

.

. -

. -

.

,

,

—

⊆

(

9

(

9

"

.

.

.

.

.

,

,

,

,

.

. -

. -

,

,

,

—

⊆

(

9

(

9

"

,

,

,

,

.

,

,

,

,

.

. -

. -

i

i

i

k

,

—

⊆

—

—

—

"

j

j

j

".

.

,

,

,

. -

.

-

i

k

.

5

where i

0" 1" 3

. j

0. The formulas characterizing e(t" k " l) are denoted

by )(t" —

" —

). where

k

l

? f

g

9

.

,

t

)(t" ." :) ⊆

—

—

.

.

:

: .

i

t

".

.

.

,

,

,

,

,

,

,

,

i

5.

.

. -

.

. -

.

. -

We require also formulas characterizing not only fixed but arbitrary config-

urations:

-

⊆ (

—

—

)

—

—

p

p

"

.

.

.

.

.

.

.

,

,

,

,

.

.

.

,

,

. -

. -

.

. -

-

⊆

—

—

—

p

p

"

,

.

.

.

.

.

,

,

,

,

,

.

.

,

,

. -

. -

.

. -

7

⊆ (

—

—

)

—

—

p

p

"

.

,

,

.

.

.

.

,

,

,

,

,

,

.

.

,

. -

. -

.

. -

7

⊆

—

—

—

p

p

.

,

,

,

.

.

.

,

,

,

,

,

,

.

.

,

. -

. -

.

. -

Now we are fully equipped to simulate the behavior of Minsky machines by

means of modal formulas. Let us consider for simplicity only tense logics

and observe that

satisfies the condition

F

x

y

z (xRzR5

y

xR5

zRy

xRy

xR5

y

x ⊆ y).

.

.

.

)

)

1

,

,

,

,

So. for every valuation in

. a formula . is true at some point in

iff the

F

F

formula

. ⊆

5

.

5

.

.

5

.

.

,,

,

,

,

,

.

.

.

#

,

,

,

,

is true at all points in

. i.e. the modal operator

can be understood

F

as "omniscience". Let ? be a formula which is refuted in

and does not

#

F

"
5(fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

contain p

and p

. With each instruction I in

we associate a formula

P

.

,

AxI by taking:

AxI ⊆

?

)(t" -

" 7

)

?

)(t

" -

" 7

)

.

.

.

,

.

-

. #

. -

. #

if I has the form t

t

" 1" 0

.

.

. h

i

AxI ⊆

?

)(t" -

" 7

)

?

)(t. " -

" 7

)

.

.

.

,

-

. #

. -

. #

if I is t

t

" 0" 1

.

.

. h

i

AxI ⊆ (

?

)(t" -

" 7

)

?

)(t

" -

" 7

))

,

.

.

.

.

-

. #

. -

. #

.

(

?

)(t" —

" 7

)

?

)(t

" —

" 7

))

.

.

.

.

.

,

.

.

-

. #

. -

. #

if I is t

t

"

1" 0

(

t

" 0" 0

).

.

.

. h

[

i

h

i

AxI ⊆ (

?

)(t" -

" 7

)

?

)(t

" -

" 7

))

.

,

.

.

.

-

. #

. -

. #

.

,

,

(

?

)(t" -

" —

)

?

)(t

" -

" —

))

.

.

.

.

.

-

. #

. -

. #

if I is t

t

" 0"

1

(

t

" 0" 0

). The formula simulating

as a whole is

.

.

P

. h

[

i

h

i

AxP ⊆

AxI .

P

I

.

:

Now. by induction on the length of computations and using the frame

in

F

Fig. 19 one can show that for every program

and configurations

s" m" n

.

P

h

i

t" k " l

. we have

:

s" m" n

t" k " l

iff

P

h

i

h

i . h

i

?

)(s" —

" —

)

?

)(t" —

" —

)

.t

AxP.

K,

m

n

k

l

.

,

.

,

-

. #

. -

. #

?

"

Thus. if the configuration problem is undecidable for

then the tense

P

calculus

.t

AxP is undecidable too. In the same manner (but using

K,

somewhat more complicated frames and formulas) one can construct unde-

"

cidable calculi in NExt

and even Ext

4 for details consult [Chagrova

K,

Int

1991] and [Chagrov and Zakharyaschev 1998]. The following table presents

some "quantitative characteristics" of known undecidable calculi in various

classes of logics. Its first line. for instance. means that there is an undecid-

able si-calculus with axioms in 5 variables and the derivability problem in

it is undecidable in the class of formulas in 3 variables4 ⊆ means that the

number of variables is optimal. and

indicates that the optimal number is

still unknown.

7

ADVANCED MODAL LOGIC

5('

Class of logics

undecidable calculi

separated formulas

The number of variables in

Ext

5"

3

⊆ 3

Int

NExt

2"

3

⊆ 1

S,

7

9

Ext

2

⊆ 1

S,

7

9

NExt

⊆ 1

⊆ 1

GL

7

Ext

⊆ 1

⊆ 1

GL

Ext

⊆ 1

⊆ 1

S

NExt

⊆ 1

⊆ 0

K,

Ext

⊆ 1

⊆ 0

K,

These observations follow from [Anderson 1983]. [Chagrov 1995]. [Sobolev

1988b]. and [Zakharyaschev 1998a]. Say that a formula : is

in

undecidable

(N)ExtL if no algorithm can determine for an arbitrary given . whether

:

L " . (respectively. :

L

.). For example. formulas in one variable.

?

?

"

the axioms of

and

are decidable in Ext

. On the other hand.

n

n

BW

BD

Int

there are purely implicative undecidable formulas in Ext

. and

Int

(p

q)

(

p

q)

(p

q)

(

p

q)

-

.

, -

-

.

, -

. -

, -

-

. -

is the shortest known undecidable formula in this class. Here are some modal

examples: the formula

(

p

p) is undecidable in NExt

.

GL

.

.

.

.

,

"

"

"

"

"

: .

,

-

.

.

.

.

.

p

p in Ext

.

in Ext

and NExt

.t4 in NExt

S

K,

K,

K

-

,

-

-

:

and NExt

.t undecidable is the conjunction of axioms of any consistent

K,

tabular logic in these classes. However. no non-trivial criteria are known for

a formula to be decidable4 it is unclear also whether one can effectively

recognize the decidability of formulas in the classes Ext

. (N)Ext

.

Int

S,

(N)Ext

. Ext

. (N)Ext

.

GL

S

K,

",. Admissibility and derivability of inference rules

Another interesting algorithmic problem for a logic L is to determine whether

an arbitrary given inference rule .

" . . . " .

,. is

in L. i.e. . is

derivable

.

n

derivable in L from the assumptions .

" . . . " .

. and whether it is

admissi5

.

n

ble

in L. i.e. for every substitution

. .

L whenever .

" . . . " .

L.

s

s

s

s

.

n

(Note that derivability depends on the postulated inference rules in L.

?

?

while admissibility depends only on the set of formulas in L.) Admissible

and derivable rules are used for simplifying the construction of derivations.

Derivable rules. like the well known rule of syllogism

.

: " :

?

.

.

"

.

?

.

may replace some fragments of fixed length in derivations. thereby short-

ening them linearly. Admissible rules in principle may reduce derivations

5)[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

more drastically. Since .

L iff the rule

,. is derivable (or admissible)

in L. the derivability and admissibility problems for inference rules may be

?

]

regarded as generalizations of the decidability problem.

If the only postulated rules in L are substitution and modus ponens. the

Deduction Theorem reduces the derivability problem for inference rules in

L to its decidability:

.

" . . . " .

n

.

is derivable in L iff .

. . .

.

:

L.

.

n

:

.

.

.

?

However. if the rule of necessitation .,

. is also postulated in L. we have

.

only

.

" . . . " .

n

.

is derivable in L iff .

" . . . " .

: .

.

n

.

L

:

"

For n-transitive L this is equivalent to

(.

. . .

.

)

:

L. and so

,

.

n

n

.

the derivability problem for inference rules in n-transitive logics is decidable

.

.

.

?

iff the logics themselves are decidable. In general. in view of the existential

quantifier in Theorem 1.1. the situation is much more complicated.

Notice first that similarly to Harrop's Theorem. a sufficient condition for

the derivability problem to be decidable in a calculus is its global FMP (see

Section 1.7). Thus we have

THEOREM 5.1

The derivability problem for inference rules in

.

.

.

K

T

D

KB

is decidable:

Moreover. sometimes we can obtain an upper bound for the parameter m

in the Deduction Theorem. which also ensures the decidability of the deriv-

ability problem for inference rules. One can prove. for instance. that for

K

it is enough to take m ⊆ 3

. In general. however. the derivability

j

ff

j

Sub

Sub

5

"

problem for inference rules in a logic L turns out to be more complex than

the decidability problem for L. (Recall. by the way. that there are logics

with FMP but not global FMP.)

THEOREM 5.3 (Spaan 1992)

NExt

There is a decidable calculus in

the

K

derivability problem for inference rules in which is undecidable:

Spaan proves this result by simulating in

. L a decidable logic defined

.

L

"

below. the following undecidable tiling problem: given a finite set of tiles

. can

tile

? The logic L is surprisingly simple:

N

N

T

T

’

L ⊆

Alt

,

p

i

(p

p

).

i

j

,,

,,

"

.

.

.

'

.

.

'

"

i

i.j

,

,

,

,

It is a subframe logic. so it is

-persistent and has FMP (because

L4

Alt

,

see Theorem 1.33 and Proposition 1.79). Note also that the bimodal logic

D

ff

ADVANCED MODAL LOGIC

5)5

L

(see Section 3.3) is a complete and elementary subframe logic which

u

is undecidable because

is undecidable. Using this observation one can

.

L

"

construct a unimodal subframe logic in NExt

with the same properties.

K

Let us turn now to the admissibility problem. It is not hard to see that

the rules

(

p

p)

p

p

p

q

r

--

.

.

, -

-

.

,

and

p

p

(

p

q)

(

p

r)

-

, --

-

.

,

-

.

are admissible but not derivable in

and

p

p,

is admissible but

Int

,

,

not derivable in any extension of

save those containing

p

p.

S,.5

.

-

:

.,

,.

in which it is derivable. (Recall that a logic L is said to be

structural ly

.

complete

if every admissible inference rule in L is derivable in L. We have

just seen that

as well as

are not structurally complete. For more

Int

S,.5

information on structural completeness see e.g.

[Tsytkin 1986. 1968] and

[Rybakov 1997].) The following result strengthens Fine's [1981] Theorem

according to which all logics in Ext

are decidable.

S,.5

THEOREM 5.2 (Rybakov 1965a)

The admissibility problem for inference

rules is decidable in every logic containing

:

S,.5

An impetus for investigations of admissible inference rules in various

logics was given by Friedman's [1987] problem 50 asking whether one can

effectively recognize admissible rules in

. This problem turned out to be

Int

closely connected to the admissibility problem in suitable modal logics. We

demonstrate this below for the logic

following [Rybakov 1968. 1969].

GL

First we show that dealing with logics in NExt

. it is sufficient to consider

K

inference rules of a rather special form. Let .(q

" . . . " q

) be a formula

.

,

",

n

containing no

and

and represented in the full disjunctive normal form.

.

,

Say that an inference rule is

if it has the form

reduced

.(p

" . . . " p

"

p

" . . . "

p

),p

.

.

.

.

n

n

,

,

THEOREM 5.5

.,:

For every rule

one can efiectively construct a reduced

rule

such that

is admissible in a logic

i,

is

.

,:

.,:

L

NExt

.

,:

K

.

.

.

.

admissible in L:

?

Proof

Observe first that if . and : do not contain p then .,: is admissible

in L iff .

(:

p),p is admissible in L. So we can consider only rules of

the form .,p

. Besides. without loss of generality we may assume that .

.

5

.

.

does not contain

. With every non-atomic subformula ? of . we associate

the new variable p

. For convenience we also put p

⊆ p

if ? ⊆ p

and

—

—

i

i

p

⊆

if ? ⊆

. We show now that the rule

—

:

:

p

5

p

p

p

: ? ⊆ ?

?

."

"

"

Sub

—

—

—

.

:

.

,

.

f

5

$

$

?

$ ? f.

,

.gg .

.

p

p

: ? ⊆

?

.

,p

Sub

—

—

.

.

.

,

,

f

5

?

g

.

5)ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

is admissible in L iff .,p

is admissible in L. For brevity we denote the

.

antecedent of that rule by .

.

.

(

) Since every substitution instance of .

,p

is admissible in L. the

.

.

8

rule .

(?

?),p

and so .,p

are also admissible in L.

—

5

Sub

.

.

.

:

5

(

) Suppose .,p

is admissible in L and .

is in L. for some substi-

s

V

.

.

⊆

tution

⊆

—

,p

: ?

.

. By induction on the construction of ?

—

—

s

Sub

one can readily show that —

?

L. Therefore. —

.

L. Since

—

5

s

s

f

?

g

.

L. we must have p

s ⊆ —

L. from which .

L and so p

L.

.

5

5

.

s

s

s

5

?

5

?

?

?

?

?

Thus .

,p

is admissible in L.

.

.

The rule .

,p

is not reduced. but it is easy to make it so simply by

.

.

representing .

in its full disjunctive normal form .

. treating subformulas

.

.

,

.

p

as variables.

i

From now on we will deal with only reduced rules different from

,p

.

:

(which is clearly admissible in any logic). Let

.

,p

be a reduced rule

j

j

.

in which every disjunct .

is the conjunction of the form

j

W

.

.

.

m

m

m

p

. . .

p

p

. . .

p

"

(18)

.

m

,

,

-

.

. -

. -

.

. -

j

where each

and

is either blank or

. We will identify such conjunc-

i

tions with the sets of their conjuncts. Now. given a non-empty set W of

-

-

-

conjunctions of the form (18). we define a frame

⊆

W" R

and a model

F

h

i

M

F

V

⊆

"

by taking

h

i

.

R.

iff

k

0" . . . " m

(

p

.

p

.

p

.

)

i

j

k

i

k

j

k

j

,

,

)

? f

g

-

?

. -

?

. -

?

.

k

0" . . . " m

(

p

.

p

.

)"

k

j

k

i

,

,

1

? f

g

-

?

.

?

V

(p

) ⊆

.

W : p

.

.

k

i

k

i

f

?

?

g

It should be clear that

is finite. transitive and irreflexive.

F

THEOREM 5.7

.

,p

j

.

j

A reduced rule

is not admissible in

i, there

GL

is a model

de.ned as above on a set

of conjunctions of the

⊆

"

W

M

F

V

form ?8]" and such that

h

i

W

(i)

p

.

for some

.

i

.

i

W

'

-

?

?

(ii) .

⊆ .

for every

i

i

.

i

W

'

j

?

(iii)

.

W

j

for every antichain

in

there is

such that. for every

a

F

k

0" . . . " m

.

⊆

p

.

i,

.

⊆

p

j

k

i

k

for some

:

.

i

,

,

a

"

?

? f

g

j

j

?

Proof

(

) We are given that there are formulas :

" . . . " :

in variables

.

m

q

" . . . " q

such that

.

and p

. where by ?

we de-

GL

GL

.

n

j

.

j

.

.

.

8

note ?

:

,p

" . . . " :

,p

. This is equivalent to

(n)

⊆

.

and

MGL

.

.

m

m

W

j

.

j

?

'?

MGL

(n)

⊆ p

. Define W to be the set of those disjuncts .

in

.

whose

f

g

j

.

.

'j

j

j

W

j

substitution instances .

are satisfied in

(n). Clearly W

⊆

. Let us

MGL

.

j

W

fl

check (i) ! (iii).

'
ADVANCED MODAL LOGIC

5)—

(i) Take a point x in

(n) at which p

is false. Since

(n)

⊆

MGL

MGL

.

.

.

. we must have x

⊆ .

for some i. One of the formulas p

or

p

is a

j

.

j

.

i

.

.

.

.

j

conjunct of .

. Clearly it is not p

. Therefore.

p

.

.

W

.

i

.

.

.

i

j

-

(ii) It suffices to show that. for all .

W and k

0" . . . " m

. .

⊆

p

i

i

k

-

?

,

,

,

iff

p

.

. Suppose .

⊆

p

. Then there is .

W such that .

R.

k

i

i

k

j

i

j

?

? f

g

j

and .

⊆ p

. By the definition of

and R. this means that p

.

j

k

k

j

V

?

j

?

and

p

.

. Conversely. suppose

p

.

. Then x

⊆ .

and in

k

i

k

i

.

i

,

,

j

?

particular x

⊆

p

for some x in

(n). Let y be a final point in the set

,

MGL

?

?

j

.

k

j

z

x

: z

⊆ p

. Since

(n) is irreflexive. we have y

⊆ p

. y

⊆

p

.

k

.

.

k

k

MGL

,

f

?

3

j

g

j

'j

and y

⊆ .

for some .

W . It follows that .

R.

and .

⊆ p

. from

j

i

j

j

k

.

j

j

?

j

which .

⊆

p

.

i

k

,

j

(iii) Let

be an antichain in

. For every .

. let x

be a final point

i

i

a

F

a

in the set

y

W

(n) : y

⊆ .

.

It should be clear that the points

GL

.

i

?

x

: .

form an antichain

in

(n) and so. by the construction of

i

i

a

b

FGL

f

?

j

g

f

?

g

FGL

FGL

b

(n). there is a point y in

(n) such that y

⊆

. Then the formula

.

W we are looking for is any one satisfying the condition y

⊆ .

. as

j

.

j

3

3

?

j

can be easily checked by a straightforward inspection.

(

) The proof in this direction is rather technical4 we confine ourselves

⊆

to just a few remarks. Let

be a model satisfying (i)!(iii). To prove that

M

.

,p

is not admissible in

we require once again the n-universal

GL

j

j

.

model

(n). but this time we take n to be the number of symbols in the

MGL

W

rule. By induction on the depth of points in

one can show that

is a

M

M

generated submodel of

(n).

MGL

Our aim is to find formulas :

" . . . " :

such that

(n)

⊆

.

and

MGL

.

m

j

.

j

j

MGL

(n)

⊆ p

(here again ?

⊆ ?

:

,p

" . . . " :

,p

). Loosely. we need

.

.

.

.

.

m

m

W

to extend the properties of

to the whole model

(n). To this end

M

MGL

'j

f

g

we can take the sets

.

in

(n) and augment them inductively in such

i

FGL

a way that we could embrace all points in

(n). At the induction step

FGL

f

g

we use the condition (iii). and the required :

" . . . " :

are constructed with

.

m

the help of (i) and (ii)4 roughly. they describe in

(n) the analogues of

MGL

the truth-sets in

of the variables in our rule.

M

.

A remarkable feature of this criterion is that it can be effectively checked.

Thus we have

THEOREM 5.6

There is an algorithm which. given an inference rule. can

decide whether it is admissible in

:

GL

In a similar way one can prove

THEOREM 5.8 (Rybakov 1968)

The admissibility problem in

is de5

Grz

cidable:

5)(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

We show now that the admissibility problem in

can be reduced to

Int

the same problem in

and so is also decidable. To this end we require

Grz

the following

THEOREM 5.6 (Rybakov 1965b)

.,:

A rule

is admissible in

i, the

Int

rule

is admissible in

:

T (.),T (:)

Grz

As a consequence of Theorems 5.8 and 5.6 we obtain

THEOREM 5.9 (Rybakov 1965b)

The admissibility problem in

is de5

Int

cidable:

Although there are many other examples of logics in which the admis-

sibility problem is decidable and the scheme of establishing decidability is

quite similar to the argument presented above. proofs are rather difficult

and only in few cases they work for big families of logics as in [Rybakov

1995]. Besides. all these results hold only for extensions of

and

.

K,

Int

For logics with non-transitive frames. even for

. the admissibility problem

K

is still waiting for a solution. The same concerns polymodal. in particular

tense logics. Chagrov [1993b] constructed a decidable infinitely axiomatiz-

able logic in NExt

for which the admissibility problem is undecidable.

K,

It would be of interest to find modal and si-calculi of that sort.

A close algorithmic problem for a logic L is to determine. given an ar-

bitrary formula .(p

" . . . " p

). whether there exist formulas :

. . . . :

such

.

n

.

n

that .(:

" . . . " :

)

L. Note that an "equation" .(p

" . . . " p

) has a so-

.

n

.

n

lution in L iff the rule .(p

" . . . " p

),

is not admissible in L. This obser-

.

n

?

vation and Theorem 5.2 provide us with examples of logics in which the

:

substitution problem is decidable (see e.g.

[Rybakov 1992]). We do not

know. however. if there is a logic such that the substitution problem in it is

decidable. while the admissibility one is not.

The inference rules we have dealt with so far were

in the sense

structural

that they were "closed" under substitution. An interesting example of a

nonstructural rule was considered by Gabbay [1961a]:

.

(

p

p)" where p

.

Sub

.

,

.

'?

.

.

It is readily seen that this rule holds in a frame

(in the sense that for every

F

formula . and every variable p not occurring in . . is valid in

whenever

F

.

(

p

p)

. is valid in

) iff

is irreflexive and that

is closed under

F

F

K

it (since

is characterized by the class of irreflexive frames). We refer the

.

,

K

reader to [Venema 1991] for more information about rules of this type.

ADVANCED MODAL LOGIC

5))

",: Properties of recursively axiomatizable logics

Dealing with infinite classes of logics. we can regard questions like "Is a

logic L decidable?". "Does L have FMP?". etc. as mass algorithmic prob-

lems. But to formulate such problems properly we should decide first how

to represent the input data of algorithms recognizing properties of logics.

One can. for instance. consider the class of recursively axiomatizable log-

ics (which. by Craig's [1972] Theorem. coincides with that of recursively

enumerable ones) and represent them as programs generating their axioms.

However. this approach turns out to be too general because the following

analog of the Rice!Uspenskij Theorem holds.

THEOREM 5.10 (Kuznetsov)

No nontrivial property of recursively axiom5

atizable siffilogics is decidable:

Of course. nothing will change if we take some other family of logics. say

NExt

. The proof of this theorem (Kuznetsov left it unpublished) is very

K,

simple4 we give it even in a more general form than required.

PROPOSITION 5.11

L

L

Suppose

and

are logics in some family

.

.

,

L

.

is recursively axiomatizable.

.

is .nitely axiomatizable ?say. by

L

L

L

.

,

,

L

a formula

". and a property

holds for only one of

.

: Then no

(

L

L

.

,

—

algorithm can recognize

. given a program enumerating axioms of a logic

P

in

:

L

P

Proof

Let —

" —

" . . . be a recursive sequence of axioms for L

. Given an

.

.

.

arbitrary (Turing. Minsky. Pascal. etc.) program

having natural numbers

P

as its input. we define the following recursive sequence of formulas (where

(n)

and (n)

are the first and second components of the pair of natural

.

,

numbers with code n under some fixed effective encoding):

—

if

does not come to a stop on input (n)

in (n)

steps

n

.

,

P

]

⊆

n

0

(

otherwise.

This sequence axiomatizes L

if

does not come to a stop on any input and

P

.

L

otherwise. It is well known in recursion theory that the halting problem

,

is undecidable. and so the property

is undecidable in

as well.

.

P

L

The reader must have already noticed that this proof has nothing to

do with modal and si-logics4 it is rather about effective computations. To

avoid this unpleasant situation let us confine ourselves to the smaller class

of

modal and si-logics and try to find algorithms rec-

.nitely axiomatizable

ognizing properties of the corresponding calculi. However. even in this case

we should be very careful. If arbitrary finite axiomatizations are allowed

then we come across the following

5)0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

THEOREM 5.13 (Kuznetsov 1962)

For every .nitely axiomatizable siffilogic

L

?in particular.

.

. inconsistent logic". there is no algorithm which.

Int

Cl

given an arbitrary .nite list of formulas. can determine whether its closure

under substitution and modus ponens coincides with

L

:

Needless to say that the same holds for (normal) modal logics as well.

Fortunately. the situation is not so hopeless if we consider finite axiom-

atizations over some basic logics. For instance. by Makinson's Theorem.

one can effectively recognize. given a formula . whether the logic

.

K

is consistent. Other examples of decidable properties in various lattices of

"

modal logics were presented in Theorems 1.69. 1.92. 1.101. and 3.28. In the

next section we consider those properties that turn out to be undecidable

in various classes of modal and si-calculi.

"," Undecidable properties of calculi

The first "negative" algorithmic results concerning properties of modal cal-

culi were obtained by Thomason [1963] who showed that FMP and Kripke

completeness are undecidable in NExt

. and consistency is undecidable in

K

NExt

.t. Later Thomason's discovery has been extended to other proper-

K

ties and narrower classes of logics. In fact. a good many standard properties

of modal and si-calculi (in reasonably big classes) proved to be undecidable4

decidable ones are rather exceptional.

In this section we present three known schemes of proving such kind of

undecidability results. Each of them has its advantages (as well as disad-

vantages) and can be adjusted for various applications. The first one is due

to Thomason [1963].

Let L(n) be a recursive sequence of normal bimodal calculi such that no

algorithm can decide. given n. whether L(n) is consistent. Such sequences.

as we shall see a bit later. exist even in NExt

.t. Suppose also that L

is

K,

.

a normal unimodal calculus which does not have some property. say. FMP.

decidability or Kripke completeness. Consider now the recursive sequence of

logics L(n)

L

with three necessity operators. If L(n) is inconsistent then

.

the fusion L(n)

L

is inconsistent too and so has the properties mentioned

&

.

&

above. And if L(n) is consistent then. in accordance with Proposition 3.7.

L(n)

L

is a conservative extension of both L(n) and L

. which means

.

.

&

that it is Kripke incomplete. undecidable and does not have FMP whenever

L

is so. Consequently. the three properties under consideration cannot be

.

decidable in the class NExt

. for otherwise the consistency of L(n) would

K

:

be decidable. By Theorem 3.16. these properties are undecidable in NExt

K

as well. Note however that. since Thomason's simulation embeds polymodal

logics only into "non-transitive" unimodal ones. this very simple scheme

ADVANCED MODAL LOGIC

5)?

does not work if we want to investigate algorithmic aspects of properties of

calculi in NExt

and Ext

.

K,

Int

To illustrate the second scheme let us recall the construction of the un-

decidable calculus in NExt

.t discussed in Section 5.1. First. we choose a

K,

Minsky program

and a configuration

⊆

s" m" n

so that no algorithm

P

a

can decide. given a configuration

. whether

:

. (That they exist is

b

a

b

P

h

i

shown in [Chagrov 1990b].) Then we put ? ⊆

and add to

.t

AxP

K,

.

one more axiom

:

"

(

?

)(s" —

" —

)

?

)(t" —

" —

))

?"

m

n

k

l

.

,

.

,

-

. #

. -

. #

.

where

⊆

t" k " l

is an arbitrary fixed configuration. The resulting calculus

c

is denoted by L(

). Suppose that

:

. Then one can readily check

c

a

c

P

h

i

that the new axiom is valid in the frame

shown in Fig. 19 and prove that

'.

F

P

:

s" m" n

t

" k

" l

iff

.

.

.

h

i . h

i

?

)(s" —

" —

)

?

)(t

.

" —

" —

)

L(

).

.

.

c

m

n

k

l

.

,

.

,

-

. #

. -

. #

?

Therefore. L(

) is undecidable. consistent and does not have FMP. And if

c

P

P

:

then L(

) is clearly inconsistent. It follows by the choice of

and

a

c

c

a

.

that consistency. decidability and FMP are undecidable in NExt

.t. In

K,

fact. the argument will change very little if we take as ? the axiom of some

tabular logic in NExt

.t. So we obtain

K,

THEOREM 5.12

The properties of tabularity and coincidence with an ar5

bitrary .xed tabular logic ?in particular. inconsistent" are undecidable in

NExt

.t

K,

Moreover. these results (except the consistency problem. of course) can

be transferred to logics in NExt

. We demonstrate this by an example4

K

complete proofs can be found in [Chagrov 1996].

We require the frame which results from that in Fig. 19 by adding to it

a reflexive point c

and an irreflexive one c

so that c

sees all other points

.

.

.

save a and b and is seen itself only from a and b. As before. we denote the

frame by

.

F

PROPOSITION 5.15

?

Let

be a formula refutable at some point in

dif5

F

ferent from

and

: Then the problem of deciding. for an

c

.

?

,

K

arbitrary formula

. whether

is undecidable:

.

. ⊆

?

K

K

] ?

"

"

"

Proof

It should be clear that ? contains at least one variable. say r. and

there are points in

at which r has distinct truth-values (under the valua-

F

tion refuting ?)4 c

and c

are then the only points in

where the formulas

.

.

F

1

⊆

r

r and

.

:

:

.

.

,

-

1

⊆

1

(r

r

r)

(

r

r

r)

.

.

,

,

,

,

,

,

,

.

,

,

.

-

,

-

,

-

5)fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

are true. respectively. Observe that from every point in

save c

we can

.

F

reach all points in

by

2 steps. So we can take

⊆

. The formulas

,

F

,

:

— and ] should be replaced with — ⊆

1

1

. ] ⊆

1

1

which

.

.

.

.

7

#

,

,

,

,

,

,

(under the valuation refuting ?) are true only at a and b. respectively. Now

.

. -

consider the logic

L(

) ⊆

AxP

(

?

)(s" —

" —

)

?

)(t" —

" —

))

?.

c

K

m

n

k

l

.

,

.

,

"

"

-

. #

. -

. #

.

If

:

then L(

) ⊆

?. And if

:

then. using the fact that

P

K

P

a

c

c

a

c

the set of points in

where ? is refutable coincides with the set of points

F

.

"

'.

from which every point of the form e(x" y " z ) is accessible by three steps.

one can show that

⊆ L(

) and so L(

)

⊆

?.

F

c

c

K

.

j

"

Putting. for instance. ? ⊆

p

p. we obtain then that the problem of

.

coincidence with Log

is undecidable in NExt

. Likewise one can prove the

K

5

following

o

THEOREM 5.17 (i)

L

If a consistent .nitely axiomatizable logic

is not a

unionffisplitting of

then the axiomatization problem for

above

is

NExt

L

K

K

undecidable:

(ii)

The properties of tabularity and coincidence with an arbitrary .xed

consistent tabular logic are undecidable in

:

NExt

K

(iii)

The problem of coincidence with an arbitrary .xed consistent calculus

in

NExt

or in

is undecidable in

NExt

NExt

D,

GL

K

:

(iv)

The properties of tabularity and coincidence with an arbitrary .xed

tabular ?in particular. inconsistent" logic are undecidable in

:

Ext

K,

Of the algorithmic problems concerning tabularity that remain open the

most intriguing are undoubtedly the tabularity and local tabularity prob-

lems in NExt

. Note that a positive solution to the former implies a

K,

positive solution to the latter.

Now we present the second scheme in a more general form used in [Cha-

grov 1990b] and [Chagrov and Zakharyaschev 1992]. Assume again that the

second configuration problem is undecidable for

and

. and let ? be a

P

a

formula such that L

? has some property

. where L

is the minimal logic

.

.

in the class under consideration. Associate with

.

and a configuration

P

a

"

P

b

a

b

a

b

a

b

formulas AxP and :(

"

) such that :(

"

)

L

AxP iff

:

.

P

.

Besides. ? and AxP are chosen so that AxP

L

?. Now consider the

?

"

.

.

?

"

calculus

L(

) ⊆ L

AxP

:(

"

)

?

( "

.

b

a

b

"

"

.

"

where ( is some formula such that (

L

?. If

:

then we clearly

.

P

a

b

have L(

) ⊆ L

? and so L(

) has

4 but if

:

then the fact

b

b

a

b

P

.

?

"

.

that L(

) does not have

must be ensured by an appropriate choice of ( .

b

"

P

'.

P

'
ADVANCED MODAL LOGIC

5)'

(In the considerations above we did not need ( . i.e. it was sufficient to put

( ⊆

). With the help of this scheme one can prove the following

]

THEOREM 5.16 (i)

The properties of decidability. Kripke completeness as

wel l as FMP are undecidable in the classes

.

.

:

Ext

(N)Ext

(N)Ext

Int

Grz

GL

(ii)

(N)Ext

The interpolation property is undecidable in

:

GL

(iii)

Ext

(N)Ext

Ext

Hal ld)en completeness is undecidable in

.

.

:

Int

Grz

S

These and some other results of that sort can be found in [Chagrov

1990b.c. 1995. 1996]. [Chagrova 1991]. [Chagrov and Zakharyaschev 1992.

1997b].

The third scheme was developed in [Chagrova 1969. 1991] and [Chagrov

and Chagrova 1997] for establishing the undecidability of certain first order

properties of modal calculi (or formulas). The difference of this scheme from

the previous one is that now we use calculi of the form

L(

) ⊆ L

AxP

:(

"

)

( "

.

b

a

b

"

"

,

where AxP satisfies one more condition besides those mentioned above:

it must be first order definable on Kripke frames for L

.

If P :

.

a

b

.

then the formula AxP

(:(

"

)

( ) is equivalent to AxP in the class of

a

b

Kripke frames for L

and so is first order definable on that class or its any

.

.

,

subclass. And if P :

then by choosing an appropriate ( one can

a

b

show that AxP

(:(

"

)

( ) is not first order definable on. say. countable

'.

a

b

Kripke frames for L

. as in [Chagrova 1969]. or on finite frames for L

. as in

.

.

.

,

[Chagrov and Chagrova 1997]. In this way the following theorem is proved:

THEOREM 5.18 (i)

No algorithm is able to recognize the .rst order de.n5

ability of modal formulas on the class of Kripke frames for

and even the

S,

.rst order de.nability on countable ?.nite" Kripke frames for

: The prop5

S,

erties of .rst order de.nability and de.nability on countable ?.nite" Kripke

frames of intuitionistic formulas are undecidable as wel l:

(ii)

The set of modal or intuitionistic formulas that are .rst order de5

.nable on countable ?.nite" frames but are not .rst order de.nable on the

class of al l ?respectively. countable" Kripke frames mentioned in ?i" is un5

decidable:

We conclude this section with two remarks. First. all undecidability

results above can be formulated in the stronger form of recursive insepa-

rability. For instance. the set of inconsistent calculi in NExt

.t and the

K,

set of calculi without FMP are recursively inseparable. And second. some

properties are not only undecidable but the families of calculi having them

are not recursively enumerable4 for example. the set of consistent calculi in

NExt

.t is not enumerable. However. for the ma jority of other properties

K,

the problem of enumerability of the corresponding calculi is open.

50[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

",5 Semantical consequence

So far we have dealt with only syntactical formalizations of logical entail-

ment. However. sometimes a semantical approach is preferable. Say that a

formula . is a

of a formula : in a class of frames

semantical consequence

if . is valid in all frames in

validating : . (One can consider also the

C

C

local. i.e. point-wise variant of this relation.) Note that . is a consequence

of : in the class of. say. Kripke frames for

iff . is a consequence of

S,

.

.

.

,

(

p

p)

(

p

p)

: in the class of all Kripke frames. But the

.

.

.

.

consequence relation on finite frames is not expressible by modal formulas

(as was shown in [Chagrov 1997]. if (

p

p)

. is valid in arbitrarily

.

.

,

large finite rooted frames then it is valid in some infinite rooted frame as

.

.

well).

In parallel with constructing and proving the undecidability of modal and

si-calculi we can obtain the following

THEOREM 5.16

The semantical consequence relation in the class of al l

?

5.

5.

5" Kripke frames is undecidable: Moreover. if

denotes one

⊆

K,

S,

Int

of these relations then there is a formula

?a formula

" such that the set

:

.

j

. : :

⊆ .

is undecidable:

f

j

g

In a sense. formulas : and . for which

. : :

⊆ .

is undecidable are

analogous to undecidable calculi and formulas. respectively. However. this

f

j

g

analogy is far from being perfect: for every formula : . the sets

. : :

.

and

. : :

.

are recursively enumerable. which contrasts with

.

f

"

g

f

"

g

THEOREM 5.19 (Thomason 1987a)

:

There exists a formula

such that

. : :

⊆ .

+

is a complete

set:

.

.

f

j

g

Unfortunately. Thomason's [1985b. 1987b. 1987c] results have not been

transferred so far to transitive frames. although this does not seem to be

absolutely impossible.

Chagrov [1990a] (see also [Chagrov and Chagrova 1997]) developed a tech-

nique for proving the analog of Theorem 5.16 for the consequence relation

on all (

-.

-.

-.

-) finite frames. Moreover. since this relation is

K,

S,

GL

Int

clearly enumerable. instead of "undecidable" one can use "not enumerable".

",' Complexity problems

Having proved that a given logic is decidable. we are facing the problem of

finding an optimal (in one sense or another) decision algorithm for it. The

complexity of decision algorithms for many standard modal and si-logics is

determined by the size of minimal frames separating formulas from those

logics. For instance. as was shown by Jaoskowski (1926) and McKinsey

ADVANCED MODAL LOGIC

505

(1951). for every .

(or .

) there is a frame

⊆

with

S,

Int

S,

F

Sub

5

'?

'?

j

3

points such that

⊆ . The same upper bound is usually

j

j

F

7

'j

obtained by the standard filtration. Is it possible to reduce the exponential

upper bound to the polynomial one? This question was raised by Kuznetsov

[1987] for

. It turned out. however. that it concerns not only

. First.

Int

Int

Kuznetsov observed (for the proof see [Kuznetsov 1989]) that if the answer

to his question is positive. i.e.

has polynomial FMP. then the problem

Int

"Are

and

polynomially equivalent?" has a positive solution as well.

Int

Cl

(Logics L

and L

are

polynomial ly equivalent

if there are polynomial time

.

,

transformations f and g of formulas such that .

L

iff f (.)

L

and

.

,

.

L

iff g(.)

L

.) Then Statman [1989] showed that the problem ".

,

.

?

?

?

?

?

Int

P SP ACE

?" is

-complete and so Kuznetsov's problem is equivalent to

one of the "hopeless" complexity problems. namely "

⊆

?".

N P

P SP ACE

Complexity function

For a logic L with FMP. we introduce the

complexity function

f

(n) ⊆ max

min

"

L

F

l

,

"

5

.

n

L

j

'

F

,

L

5,

F

5j

'

,

j

j

where l(.). the

of . is the number of subformulas in . and

the

length

F

number of points in

. If there is a constant c such that

F

j

j

f

(n)

3

fl

(or f

(n)

n

or f

(n)

c

n)"

L

L

L

c

n

c

7

7

7

6

L is said to have the

(respectively.

or

)

exponential

polynomial

linear

.nite

model property

. The following result shows that

does not have polyno-

Int

mial FMP.

THEOREM 5.30 (Zakharyaschev and Popov 1989) log

f

(n)

n

:

Int

,

*

Proof

The exponential upper bound is well known and to establish the

lower one it is sufficient to use the formulas

n

.

5

]

⊆

((

p

q

)

(p

q

)

q

)

(

p

q

)

(p

q

).

n

i

i

i

i

i

".

".

".

".

.

.

.

.

-

.

,

.

.

.

-

.

,

.

i

5.

.

It is not hard to see that ]

,

and every refutation frame for ]

contains

n

n

Int

the full binary tree of depth n as a subframe.

?

.

Likewise the same result can be proved for many other standard super-

intuitionistic and modal logics whose FMP is established by the usual ,l-

tration and whose frames contain full binary trees of arbitrary finite depth.

Such are. for instance.

.

.

.

.

. In the case of

the length of

KC

SL

K,

S,

GL

K

50ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

formulas that play the role of ]

is not a linear but a square function of n.

n

which means that f

(n)

3

. for some constant c " 0. and so

does

fl

K

K

pc

n

not have polynomial FMP either. As was shown in [Zakharyaschev 1996].

9

all cofinal subframe modal and si-logics have exponential FMP. It seems

plausible that log

f

(n)

n for every consistent si-logic L different from

,

L

*

Cl

and axiomatizable by formulas in one variable.

The construction of Theorem 5.30 does not work for logics whose frames

do not contain arbitrarily large full binary trees. Such are. for instance.

logics of finite width or of finite depth. and the following was proved in

[Chagrov 1962].

THEOREM 5.31 (i)

n 5 '

NExt

NExt

The minimal logics of width

in

.

.

K,

S,

NExt

.

.

have polynomial FMP:

NExt

Ext

Grz

GL

Int

(ii)

and al l logics containing

have linear FMP:

Lin

S,.5

(iii)

n

NExt

NExt

Ext

The minimal logics of depth

in

.

.

have

Grz

GL

Int

polynomial FMP. with the power of the corresponding polynomial

n

1

:

(iv)

n

NExt

NExt

The minimal logics of depth

in

.

have polynomial

K,

S,

7

[

FMP. with the power of the corresponding polynomial

n

:

7

Proof

(i) is proved by two filtrations. First. with the help of the standard

filtration one constructs a finite frame separating a formula . from the given

logic L and then. using the selective filtration. extracts from it a polynomial

separation frame:

it suffices to take a point refuting . and all maximal

points at which : is false. for some

:

. (in the intuitionistic case

.

Sub

:

?

. should be considered). (ii) is proved analogously.

Sub

?

.

?

To illustrate the proof of (iii) and (iv). we consider the minimal logic L of

depth 2 in NExt

. Suppose . ,

L. Then there is a transitive irreflexive

GL

model

of depth

2 refuting . at its root r. Let

:

. for 1

i

m. be

i

M

.

?

all "boxed" subformulas of . For every i

1" . . . " m

. we choose a point

7

7

7

refuting :

. if it exists. And then we do the same in the set x

. for every

i

? f

g

chosen point x. Let

be the submodel formed by the selected points and

.

M

3

r. Clearly. it contains at most 1 " m " m

points. And by induction on the

,

construction of formulas in

. one can easily show that

refutes . at

.

Sub

M

r.

To prove the lower bound one can use the formulas

n

n

—

⊆

(

(p

p

)

(q

q

)

n

i

i

i

i

".

".

.

.

-

.

.

.

.

i

5.

.

i

5.

.

n

n

,

,

.

.

,

,

(

(

p

p

))

(

(

q

q

)))

i

i

".

i

i

".

"

i

5.

.

i

5.

.

] .

-

.

.

: .

-

.

which are not in L and every separation frame for which contains the full

n-ary tree of depth 2. i.e. at least 1 " n " n

points.

,

.

ADVANCED MODAL LOGIC

50—

a

a

a

a

b

b

b

n

.

,

:

.

,

f

n

1

9

. .

.

.

.

5

5

5

6 6 6

5

o

5

5

6 6 6

5

Figure 30.

However. even if frames for a logic with FMP do not contain full finite

binary trees its complexity function can grow very fast. witness the following

result of [Chagrov 1967a].

THEOREM 5.33

f (n)

L

For every arithmetic function

. there are logics

of

width 8 in

and of width

in

.

.

having

NExt

3

Ext

NExt

NExt

K,

Int

Grz

GL

FMP and such that

f

(n)

f (n)

:

L

9

Proof

K,

5

We construct a logic L

NExt

.

whose complexity function

grows faster than a given increasing arithmetic function f (n). Define L to

?

be the logic of all frames of the form shown in Fig. 30. To see that L satisfies

the property we need. consider the sequence of formulas

]

⊆ p

(

p

(

(

p

p)

p))"

.

.

.

.

.

.

.

,

.

.

.

]

⊆ p

(

p

]

).

i

i

i

i

".

".

".

.

.

,

.

Since these formulas are refuted at points of the form a

in sufficiently large

j

frames depicted in Fig. 30. they are not in L. And since L contains the

formulas

]

(

5

)"

n

,

,

.

f

n

f

n

1

9

.

1

9

-

.

] .

:

]

cannot be separated from L by a frame with

f (n) points.

n

.

7

For logics of finite depth this theorem does not hold. since according

to the description of finitely generated universal frames in Section 1.3. for

every L

NExt

(k

2). we have

k

KfiBD

?

9

.

c

n

.

'

'

'

3

k

,

-

5

f

(n)

3

L

7

for some constant c " 0. And as was shown in [Chagrov 1967a]. one cannot

in general reduce this upper bound.

THEOREM 5.32

k

2

L

k

NExt

For every

. there are logics

of depth

in

.

Grz

NExt

Ext

.

such that

GL

Int

9

n

.

'

'

'

3

k

,

5

f

(n)

3

.

L

-

9

50(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

Proof

GL

We illustrate the proof for k ⊆ 2 in NExt

. Let L be the logic

characterized by the class of rooted frames

for

of depth 2 defined

m

F

GL

as follows.

contains m dead ends. every non-empty set of them has a

m

F

focus. i.e. a point that sees precisely the dead ends in this set. and besides

the root there are no other points in

. It should be clear that L does not

m

F

contain the formulas

n

n

(

⊆

(p

p

)

(p

p

).

m

i

i

i

i

".

".

.

.

i

5.

.

i

5.

.

.

.

.

On the other hand (

is not refutable in a frame for L with 5 3

points

n

m

because the following formulas are in L:

(

m

(

9

i

9

)"

i

,

,

,

-

.

.

-

X

:""":m

.

:X

.

5

i

X

.

i

X:

i

m

.

.

[f

g

—

:

":

,

,

where 9

⊆ p

. . .

p

p

. . .

p

.

i

i

i

.

".

m

".

.

.

.

. -

.

. -

Note. however. that the logics constructed in the proofs of the last two

theorems are not finitely axiomatizable. We know of only one "very com-

plex" calculus with FMP.

THEOREM 5.35 log

log

f

(n)

n

:

KP

,

,

*

For the proof see [Chagrov and Zakharyaschev 1998]. where the reader

can find also some other results in this direction.

Relation to complexity classes

Let us return to the original problem of optimizing decision algorithms for

the logics under consideration. First of all. it is to be noted that there is

a natural lower bound for decision algorithms which cannot be reduced—

we mean the complexity of decision procedures for

. This is clear for

Cl

(consistent) modal logics on the classical base4 and by Glivenko's Theorem.

every si-logic "contains"

in the form of the negated formulas. Thus.

Cl

if we manage to construct an effective decision procedure for some of our

logics then

can be decided by an equally effective algorithm. (We remind

Cl

the reader that all existing decision algorithms for

require exponential

Cl

time (of the number of variables in the tested formulas). On the other

hand. only polynomial time algorithms are regarded to be acceptable in

complexity theory.)

So. when analyzing the complexity of decision algorithms for modal and

si-logics. it is reasonable to compare them with decision algorithms for

.

Cl

For example. if a logic L is polynomially equivalent to

then we can regard

Cl

"
ADVANCED MODAL LOGIC

50)

these two logics to be of the same complexity. Moreover. provided that

somebody finds a polynomial time decision procedure for

. a polynomial

Cl

time decision algorithm can be constructed for L as well. The following

theorem lists results obtained by [Ladner 1988]. [Ono and Nakamura 1960].

[Chagrov 1962]. and [Spaan 1992].

THEOREM 5.37

Al l logics mentioned in the formulation of Theorem [:08

are polynomial ly equivalent to

:

Cl

Proof

We illustrate the proof only for the minimal logic L of depth 2 in

NExt

using the method of [Kuznetsov 1989]. Suppose . is a formula

GL

of length n. By Theorem 5.31. the condition .

L means that

⊆ .

M

for some model

⊆

"

based on a frame

for

of depth

2 and

M

F

V

F

GL

'?

'j

cardinality

c

n

. We describe this observation by means of classical

,

h

i

7

formulas. understanding their variables as follows. Let x. y . z be names

7

6

(numbers) of points in

. for 1

x" y " z

c

n

. With every pair

x" y

of

F

,

points in

we associate a variable p

whose meaning is "x sees y". And

xy

F

7

7

6

h

i

with every :

. and every x we associate a variable q

which means

Sub

x

"

": is true at x". Denote by — the conjunction

?

5

5

5

q

q

. . .

q

:

.

.

,

c

n

.

.

.

fl

It means that . is true in

. And let ] be the conjunction of the following

M

formulas under all possible values of their subscripts:

p

" p

p

p

" q9

q

"

xx

xy

yz

xz

x

x

"

"

-

.

.

5 -

"

—

"

—

"

—

"

—

"

"

q

6

q

q

" q

]

q

q

" q

(p

q

).

xy

x

x

x

x

x

x

x

y

5

.

5

,

5

.

y

5.

.

:

c

n

.

fl

(The first two formulas say that R is irreflexive and transitive and the rest

simulate the truth-relation in

.) Finally. we define a formula saying that

M

our frame is of depth

2:

7

( ⊆

(p

p

p

).

xy

yz

zu

.

x:y :z:u

.

c

n

,

,

fl

-

.

.

:

,

"

The formula ]

(

— is of length

70(c

n

)

and can be clearly constructed

by an algorithm working at most linear time of the length of . It is readily

.

.-

7

6

seen that .

L iff ]

(

— is satisfiable in

. Thus we have polynomially

Cl

reduced the derivability problem in L to that in

. Since the converse

Cl

'?

.

. -

reduction is trivial. L and

are polynomially equivalent.

Cl

.

The reader must have noticed that Theorem 5.37 lists almost all logics

known to have polynomial FMP. Kuznetsov [1987] conjectured that every

500

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

calculus having polynomial FMP is polynomially equivalent to

. This

Cl

conjecture is closely related to some problems in the complexity theory of

algorithms. We remind the reader that

is the class of problems that

N P

can be solved by polynomial time algorithms on nondeterministic (Turing)

machines. An

-complete problem is a problem in

to which all other

N P

N P

problems in

are polynomially reducible. (For more detailed definitions

N P

consult [Garey and Johnson 1989].) The most popular

-complete prob-

N P

lem is the satisfiability problem for Boolean formulas. i.e. the nonderiv-

ability problem for

. So the nonderivability problem for all logics listed

Cl

Theorem 5.37 is

-complete and Kuznetsov's conjecture is equivalent to

N P

a positive solution to the problem whether the nonderivability problem for

every calculus with polynomial FMP is

-complete.

N P

Note that if

⊆

(for the definition of the class

see

coN P

N P

coN P

[Garey and Johnson 1989]4 we just mention that the derivability problem

in

is

-complete) then Kuznetsov's conjecture does hold. But

Cl

coN P

since "

⊆

?" belongs to the list of "unsolvable" problems un-

coN P

N P

der the current state of knowledge. it may be of interest to find out whether

Kuznetsov's conjecture implies

⊆

.

coN P

N P

Another complexity class we consider here is the class

of

P SP ACE

problems that can be solved by polynomial space algorithms. A typical

example of a

-

complete

problem is the truth problem for quan-

P SP ACE

tified Boolean formulas. The following theorem (which summarizes results

obtained by Ladner [1988]. Statman [1989]. Chagrov [1967a]. Halpern and

Moses [1993] and Spaan [1992]) lists some

-complete logics.

P SP ACE

THEOREM 5.36

The nonderivability problem ?and so the derivability prob5

lem" in the fol lowing logics is

5complete"

.

.

.

.

P SP ACE

Int

KC

K

K

K

S,

S,

S,

S.

S.

GL

Grz

K

K,

.

.

.

.

.

and

.t

.t

:

&

&

&

It follows in particular that complexity is not preserved under the for-

mation of fusions of logics (under the assumption

⊆

).

N P

P SP ACE

since nonderivability in

is

-complete. For more information on the

S.

N P

preservation of complexity under fusions consult [Spaan 1992].

Finally we note that the nonderivability problem in logics with the univer-

sal modality or common knowledge operator is mostly even

-

EXP T IM E

complete. witness

[Spaan 1992] and

[Halpern and Moses 1993].

K

SfiEC

u

,

7 APPENDIX

We conclude this chapter with a (by no means complete) list of references for

those directions of research in modal logic that were not considered above:

Congruential logics:

These are modal logics that do not necessar-

5

ily contain the distribution axiom

(p

q)

(

p

q) but are

.

.

.

.

.

.

'
ADVANCED MODAL LOGIC

50?

closed under modus ponens and the congruence rule p

q,

p

q .

.

.

Segerberg [1981] and Chellas [1960] define a semantics for these logics4

5

5

Lewis [1985] proves FMP of all congruential non-iterative logics and

Surendonk [1996] shows that they are canonical. Do)sen [1966] consid-

ers duality between algebras and neighbourhood frames and Kracht

and Wolter [1998a] study embeddings into normal bimodal logics.

Modal logics with graded modalities

. The truth-relation for their pos-

sibility operators

is defined as follows: x

⊆

p iff there exist at

n

n

,

,

least n points accessible from x at which p holds. An early reference

j

is [Fine 1983]4 more recent are [van der Hoek 1993] (applications to

epistemic logic) and [Cerrato 1995] (FMP and decidability).

Modal logics with the difierence operator

nominals

names

or with

(or

).

The semantics of nominals is similar to that of propositional variables4

the difference is that a nominal is true at exactly one point in a frame.

For the difference operator [

⊆]. we have x

⊆ [

⊆]p iff p is true every-

where except x. De Rijke [1992]. Blackburn [1992] and Goranko and

j

Gargov [1992] study the completeness and expressive power of systems

of that sort. Closely related to the difference operator is the modal

operator [i] for inaccessible worlds: x

⊆ [i]p iff p is true in all worlds

which are not accessible from x. see [Humberstone 1962] and [Goranko

j

1990a].

Modal logics with dyadic

polyadic operators

or even

. For duality theory

in this case see [Goldblatt 1969]. An extensive study of Sahlqvist-

type theorems with applications to polyadic logics is [Venema 1991].

For connections with the theory of relational algebras see [Mikulas

1997] and [Marx 1997]. In those dissertations the reader can find also

recent results on arrow logic. i.e. a certain type of polyadic logic which

is interpreted in Kripke frames built from arrows. An embedding

of polyadic logics into polymodal logics is discussed in [Kracht and

Wolter 1998b].

Bisimulations

. Bisimulations were introduced in modal logic by van

Benthem [1962] to characterize its expressive power4 see also [de Rijke

1996]. Visser [1996] used bisimulations to prove uniform interpolation.

Recently. bisimulations have attracted attention because they form a

common tool in modal logic and process theory. We refer the reader

to collection [Ponse

1996] for information on this sub ject.

et al:

Modal logics with .xed point operators

. i.e. modal logics enriched by

operators forming the least and greatest fixed points of monotone

formulas. These systems are also called

5-

. Under this

modal

calculi

5

5

5

5

5

'
'
50fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

name they were introduced and studied by Kozen [1962. 1966]4 see

also [Walukiewicz 1992. 1996] and [Bosangue and Kwiatkowska 1996].

Proof theory

. Early references to studies of sequent calculi and natural

5

deduction systems for a few modal logics can be found in

Basic Modal

Logic

. More recently. (non-standard) sequent calculi for modal log-

ics have been considered by Do)sen [1967b]. Masini [1993] and Avron

[1996]4 see also collection [Wansing 1996] and the chapter

Sequent

systems for modal logics

in this Handbook. For natural deduction

systems see Borghuis [1992]4 tableau systems for modal and tense

logics were constructed in [Fitting 1962]. [Rautenberg 1962]. [Gore

1995] and [Kashima 1995]. Orlowska [1996] develops

relational proof

systems

. Display calculi for modal logics were introduced by Belnap

[1963]4 see also [Wansing 1995] and collection [Wansing 1996].

REFERENCES

"

"

Amati and Pirri- 5''(

G8 Amati and F8 Pirri8 A uniform tableau method for intuition2

istic modal logics I8 Studia Logica- )—3ff'.0[- 5''(8

"

"

Anderson- 5'?ff

J8G8 Anderson8 Superconstructive propositional calculi with extra ax2

iom schemes containing one variable8 Zeitschrift ffiur Mathematische Logik und Grund.

lagen der Mathematik- 5fl355—.5—[- 5'?ff8

"

"

Avron- 5''0

A8 Avron8 The method of hypersequents in the proof therory of propo2

sitional non2classical logics8 In W8 Hodges- M8 Hyland- C8 Steinhorn- and J8 Truss-

editors- Logic. from Foundations to Applications- pages 5.—ff8 Clarendon Press- Ox2

ford- 5''08

"

"

Barwise and Moss- 5''0

J8 Barwise and L8 Moss8 Vicious Circles8 CSLI Publications-

Stanford- 5''08

"

"

Beklemishev- 5''(

L8D8 Beklemishev8 On bimodal logics of provability8 Annals of Pure

and Applied Logic- 0fl355).5)'- 5''(8

"

"

Beklemishev- 5''0

L8D8 Beklemishev8 Bimodal logics for extensions of arithmetical

theories8 Journal of Symbolic Logic- 053'5.5ff(- 5''08

"

"

Bellissima- 5'fl(

F8 Bellissima8 Atoms in modal algebras8 Zeitschrift ffiur Mathematische

Logik und Grund lagen der Mathematik- —[3—[—.—5ff- 5'fl(8

"

"

Bellissima- 5'fl)

F8 Bellissima8 An e4ective representation for :nitely generated free

interior algebras8 Algebra Universalis- ff[3—[ff.—5?- 5'fl)8

"

"

K.Alt

n

Bellissima- 5'flfl

F8 Bellissima8 On the lattice of extensions of the modal logic

8

Archive of Mathematical Logic- ff?35[?.55(- 5'flfl8

"

"

Bellissima- 5''5

F8 Bellissima8 Atoms of tense algebras8 Algebra Universalis- fffl3)ff.?fl-

5''58

"

"

Belnap- 5'flff

N8D8 Belnap8 Display logic8 Journal of Philosophical Logic- 553—?).(5?-

5'flff8

"

"

Beth- 5')—

E8W8 Beth8 On Padua6s method in the theory of de:nitions8 Indagationes

Mathematicae- 5)3——[.——'- 5')—8

"

"

Bezhanishvili- 5''?

G8 Bezhanishvili8 Modal intuitionistic logics and superintuitionistic

predicate logics3 correspondence theory8 Manuscript- 5''?8

"

"

Blackburn- 5''—

P8 Blackburn8 Nominal tense logic8 Notre Dame Journal of Formal

Logic- —(3)0.fl—- 5''—8

"

"

Blok and Kfiohler- 5'fl—

W8J8 Blok and P8 Kfiohler8 Algebraic semantics for quasi2classical

modal logics8 Journal of Symbolic Logic- (fl3'(5.'0(- 5'fl—8

ADVANCED MODAL LOGIC

50'

"

"

Blok and Pigozzi- 5'flff

W8 Blok and D8 Pigozzi8 On the structure of varieties with

equationally de:nable principal congruences I8 Algebra Universalis- 5)35').ffff?- 5'flff8

"

"

Blok- 5'?0

W8J8 Blok8 Varieties of interior algebras8 PhD thesis- University of Ams2

terdam- 5'?08

"

"

Blok- 5'?fl

W8J8 Blok8 On the degree of incompleteness in modal logics and the cov2

ering relation in the lattice of modal logics8 Technical Report ?fl2[?- Department of

Mathematics- University of Amsterdam- 5'?fl8

"

"

Blok- 5'fl[a

W8J8 Blok8 The lattice of modal algebras is not strongly atomic8 Algebra

Universalis- 553fffl).ff'(- 5'fl[8

"

"

Blok- 5'fl[b

W8J8 Blok8 The lattice of modal logics3 an algebraic investigation8 Journal

of Symbolic Logic- ()3ffff5.ff—0- 5'fl[8

"

"

Blok- 5'fl[c

W8J8 Blok8 Pretabular varieties of modal algebras8 Studia Logica- —'35[5.

5ff(- 5'fl[8

"

"

Boolos- 5''—

G8 Boolos8 The Logic of Provability8 Cambridge University Press- 5''—8

"

"

Borghuis- 5''—

T8 Borghuis8 Interpreting modal natural deduction in type theory8 In

M8 de Rijke- editor- Diamonds and Defaults- pages 0?.5[ff8 Kluwer Academic Pub2

lishers- 5''—8

"

"

Bosangue and Kwiatkowska- 5''0

M8 Bosangue and M8 Kwiatkowska8 Re2interpreting

the modal

2calculus8 In A8 Ponse- M8 de Rijke- and Y8 Venema- editors- Modal Logic

:

and Process Algebra- pages 0).fl—8 CSLI publications- Stanford- 5''08

"

"

Bo;ziΦc and Do;sen- 5'fl(

M8 Bo;ziΦc and K8 Do;sen8 Models for normal intuitionistic logics8

Studia Logica- (—3ff5?.ff()- 5'fl(8

"

"

Bfiuchi and Siefkes- 5'?—

J8R8 Bfiuchi and D8 Siefkes8 The monadic second order theory

of al l countable ordinals8 Number —fffl in Lecture Notes in Mathematics8 Springer-

5'?—8

"

"

Bfiuchi- 5'0ff

J8R8 Bfiuchi8 On a decision method in restricted second order arithmetic8 In

Logic: Methodology and Philosophy of Science. Proceedings of the "5'? International

Congress- pages 5.558 Stanford University Press- 5'0ff8

"

"

M I P C

Bull- 5'00a

R8A8 Bull8

as the formalization of an intuitionistic concept of

modality8 Journal of Symbolic Logic- —530['.050- 5'008

"

"

S

.

Bull- 5'00b

R8A8 Bull8 That all normal extensions of

(

— have the :nite model prop2

erty8 Zeitschrift ffiur Mathematische Logik und Grund lagen der Mathematik- 5ff3—(5.

—((- 5'008

"

"

Bull- 5'0fl

R8A8 Bull8 An algebraic study of tense logic with linear time8 Journal of

Symbolic Logic- ——3ff?.—fl- 5'0fl8

"

"

Cerrato- 5''(

C8 Cerrato8 Decidability by :ltrations for graded normal logics8 Studia

Logica- )—305.?—- 5''(8

"

"

Chagrov and Chagrova- 5'')

A8V8 Chagrov and L8A8 Chagrova8 Algorithmic problems

concerning :rst order de:nability of modal formulas on the class of all :nite frames8

Studia Logica- ))3(ff5.((fl- 5'')8

"

"

Chagrov and Zakharyaschev- 5''5

A8V8 Chagrov and M8V8 Zakharyaschev8 The dis2

junction property of intermediate propositional logics8 Studia Logica- )[30—.?)- 5''58

"

"

Chagrov and Zakharyaschev- 5''ff

A8V8 Chagrov and M8V8 Zakharyaschev8 Modal

companions of intermediate propositional logics8 Studia Logica- )53('.flff- 5''ff8

"

"

Chagrov and Zakharyaschev- 5''—

A8V8 Chagrov and M8V8 Zakharyaschev8 The unde2

cidability of the disjunction property of propositional logics and other related prob2

lems8 Journal of Symbolic Logic- )fl3('.flff- 5''—8

"

"

Chagrov and Zakharyaschev- 5'')a

A8V8 Chagrov and M8V8 Zakharyaschev8 On the

independent axiomatizability of modal and intermediate logics8 Journal of Logic and

Computation- )3fffl?.—[ff- 5'')8

"

"

Chagrov and Zakharyaschev- 5'')b

A8V8 Chagrov and M8V8 Zakharyaschev8 Sahlqvist

formulas are not so elementary even above

(8

In L8 Csirmaz- D8M8 Gabbay- and

S

M8 de Rijke- editors- Logic Col loquium"51- pages 05.?—8 CSLI Publications- Stanford-

5'')8

"

"

Chagrov and Zakharyaschev- 5''?

A8V8 Chagrov and M8V8 Zakharyaschev8 Modal

Logic8 Oxford University Press- 5''?8

5?[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Chagrov- 5'fl—

A8V8 Chagrov8 On the polynomial approximability of modal and super2

intuitionistic logics8 In Mathematical Logic: Mathematical Linguistics and Algorithm

Theory- pages ?).fl—8 Kalinin State University- Kalinin- 5'fl—8 ]Russian78

"

"

Chagrov- 5'fl)a

A8V8 Chagrov8 On the complexity of propositional logics8 In Complex.

ity Problems in Mathematical Logic- pages fl[.'[8 Kalinin State University- Kalinin-

5'fl)8 ]Russian78

"

"

Chagrov- 5'fl)b

A8V8 Chagrov8 Varieties of logical matrices8 Algebra and Logic- ff(3ff?fl.

—ff)- 5'fl)8

"

"

Chagrov- 5'fl'

A8V8 Chagrov8

Nontabularity.pretabularity- antitabularity-

co2

antitabularity8 In Algebraic and Logical Constructions- pages 5[).5558 Kalinin State

University- Kalinin- 5'fl'8 ]Russian78

"

"

Chagrov- 5''[a

A8V8 Chagrov8 Undecidability of the :nitary semantical consequence8

In Proceedings of the XXth USSR Conference on Mathematica Logic: Alma.Ata- page

50ff- 5''[8 ]Russian78

"

"

Chagrov- 5''[b

A8V8 Chagrov8 Undecidable properties of extensions of provability

logic8 I8 Algebra and Logic- ff'3ff—5.ff(—- 5''[8

"

"

Chagrov- 5''[c

A8V8 Chagrov8 Undecidable properties of extensions of provability

logic8 II8 Algebra and Logic- ff'3([0.(5—- 5''[8

"

"

Chagrov- 5''ffa

A8V8 Chagrov8 Continuality of the set of maximal superintuitionistic

logics with the disjunction property8 Mathematical Notes- )535flfl.5'—- 5''ff8

"

"

Chagrov- 5''ffb

A8V8 Chagrov8 A decidable modal logic with the undecidable admis2

sibility problem for inference rules8 Algebra and Logic- —53)—.))- 5''ff8

"

"

Chagrov- 5''(

A8V8 Chagrov8 Undecidable properties of superintuitionistic logics8 In

S8V8 Jablonskij- editor- Mathematical Problems of Cybernetics- volume )- pages 0?.

5[fl8 Physmatlit- Moscow- 5''(8 ]Russian78

"

"

Chagrov- 5'')

A8V8 Chagrov8 One more :rst2order e4ect in Kripke semantics8

In

Proceedings of the "?th International Congress of Logic: Methodology and Philosophy

of Science- page 5ff(- Florence- Italy- 5'')8

"

"

Chagrov- 5''0

A8V8 Chagrov8

Tabular modal

logics3

algorithmic problems8

Manuscript- 5''08

"

"

Chagrova- 5'fl0

L8A8 Chagrova8 On the :rst order de:nability of intuitionistic for2

mulas with restrictions on occurrences of the connectives8 In M8I8 Kanovich- editor-

Logical Methods for Constructing E9ective Algorithms- pages 5—).5—08 Kalinin State

University- Kalinin- 5'fl08 ]Russian78

"

"

Chagrova- 5'fl'

L8A8 Chagrova8 On the problem of de8nability of propositional formu.

las of intuitionistic logic by formulas of classical 8rst order logic8 PhD thesis- Kalinin

State University- 5'fl'8 ]Russian78

"

"

Chagrova- 5''[

L8A8 Chagrova8 On the preservation of :rst order properties under the

embedding of intermediate logics into modal logics8 In Proceedings of the Xth USSR

Conference for Mathematical Logic- page 50—- 5''[8 ]Russian78

"

"

Chagrova- 5''5

L8A8 Chagrova8 An undecidable problem in correspondence theory8

Journal of Symbolic Logic- )035ff05.5ff?ff- 5''58

"

"

Chellas and Segerberg- 5''(

B8 Chellas and K8 Segerberg8 Modal logics with the

MacIntosh2rule8 Journal of Philosophical Logic- ff—30?.fl0- 5''(8

"

"

Chellas- 5'fl[

B8F8 Chellas8 Modal Logic. An Introduction8 Cambridge University

Press- 5'fl[8

"

"

Craig- 5')—

W8 Craig8 On axiomatizability within a system8 Journal of Symbolic Logic-

5fl3—[.—ff- 5')—8

"

"

Craig- 5')?

W8 Craig8 Three uses of the Herbrandt.Gentzen theorem in relating model

theory and proof theory8 Journal of Symbolic Logic- ffff3ff0'.fffl)- 5')?8

"

"

Cresswell- 5'fl(

M8J8 Cresswell8 An incomplete decidable modal logic8 Journal of Sym.

bolic Logic- ('3)ff[.)ff?- 5'fl(8

"

"

Day- 5'??

A8 Day8 Splitting lattices generate all lattices8 Algebra Universalis- ?350—.

5?[- 5'??8

"

"

de Rijke- 5''—

M8 de Rijke8 Extending Modal Logic8 PhD thesis- Universiteit van

Amsterdam- 5''—8

ADVANCED MODAL LOGIC

5?5

"

"

de Rijke- 5''0

M8 de Rijke8 A Lindstrfiom theorem for modal logic8

In A8 Ponse-

M8 de Rijke- and Y8 Venema- editors- Modal Logic and Process Algebra- pages ff5?.ff—[8

CSLI Publications- Stanford- 5''08

"

"

Diego- 5'00

A8 Diego8 Sur les alg0ebres de Hilbert8 Gauthier2Villars- Paris- 5'008

"

"

Doets- 5'fl?

K8 Doets8 Completeness and de8nability8 PhD thesis- Universiteit van

Amsterdam- 5'fl?8

"

"

Do;sen- 5'fl)a

K8 Do;sen8 Models for stronger normal intuitionistic modal logics8 Studia

Logica- ((3—'.?[- 5'fl)8

"

"

Do;sen- 5'fl)b

K8 Do;sen8 Sequent2systems for modal logic8 Journal of Symbolic Logic-

)[35('.5)'- 5'fl)8

"

"

Do;sen- 5'flfl

K8 Do;sen8 Duality between modal algebras and neighbourhood frames8

Studia Logica- (fl3ff5'.ff—(- 5'flfl8

"

"

DrabbΦe- 5'0?

J8 DrabbΦe8 Une proprietΦe des matrices caractΦeristiques des syst⊆emes

5-

S

S

S

ff- et

—8 Comptes Rendus de l"Acadffemie des Sciences: Paris- ff0)3A5- 5'0?8

"

"

Dugundji- 5'([

J8 Dugundji8 Note on a property of matrices for Lewis and Langford6s

calculi of propositions8 Journal of Symbolic Logic- )35)[.5)5- 5'([8

"

"

Dummett and Lemmon- 5')'

M8A8E8 Dummett and E8J8 Lemmon8 Modal logics be2

tween

( and

)8 Zeitschrift ffiur Mathematische Logik und Grund lagen der Mathe.

S

S

matik- )3ff)[.ff0(- 5')'8

"

"

Dummett- 5')'

M8A8E8 Dummett8 A propositional calculus with denumerable matrix8

Journal of Symbolic Logic- ff(3'?.5[0- 5')'8

"

"

Ershov- 5'fl[

Yu8L8 Ershov8 Decision problems and constructive models8 Nauka-

Moscow- 5'fl[8 ]Russian78

"

"

Esakia and Meskhi- 5'??

L8L8 Esakia and V8Yu8 Meskhi8 Five critical systems8 Theo.

ria- ([3)ff.0[- 5'??8

"

"

Esakia- 5'?(

L8L8 Esakia8 Topological Kripke models8 Soviet Mathematics Doklady-

5)35(?.5)5- 5'?(8

"

"

Esakia- 5'?'a

L8L8 Esakia8 On varieties of Grzegorczyk algebras8 In A8 I8 Mikhailov- ed2

itor- Studies in Non.classical Logics and Set Theory- pages ff)?.fffl?8 Moscow- Nauka-

5'?'8 ]Russian78

"

"

Esakia- 5'?'b

L8L8 Esakia8 To the theory of modal and superintuitionistic systems8 In

V8A8 Smirnov- editor- Logical Inference- Proceedings of the USSR Symposium on the

Theory of Logical Inference- pages 5(?.5?ff8 Nauka- Moscow- 5'?'8 ]Russian78

"

"

Ewald- 5'fl0

W8B8 Ewald8 Intuitionistic tense and modal logic8 Journal of Symbolic

Logic- )53500.5?'- 5'fl08

"

"

Ferrari and Miglioli- 5''—

M8 Ferrari and P8 Miglioli8 Counting the maximal interme2

diate constructive logics8 Journal of Symbolic Logic- )fl35—0).5([fl- 5''—8

"

"

Ferrari and Miglioli- 5'')a

M8 Ferrari and P8 Miglioli8 A method to single out maximal

propositional logics with the disjunction property8 I8 Annals of Pure and Applied Logic-

?035.(0- 5'')8

"

"

Ferrari and Miglioli- 5'')b

M8 Ferrari and P8 Miglioli8 A method to single out maximal

propositional logics with the disjunction property8 II8 Annals of Pure and Applied

Logic- ?0355?.50fl- 5'')8

"

"

Fine and Schurz- 5''0

K8 Fine and G8 Schurz8 Transfer theorems for strati:ed modal

logics8 In J8 Copeland- editor- Logic and Reality: Essays in Pure and Applied Logic-

In memory of Arthur Prior- pages 50'.ff5—8 Oxford University Press- 5''08

"

"

S

.

Fine- 5'?5

K8 Fine8 The logics containing

(

—8 Zeitschrift ffiur Mathematische Logik

und Grund lagen der Mathematik- 5?3—?5.—?0- 5'?58

"

"

Fine- 5'?ff

K8 Fine8 In so many possible worlds8 Notre Dame Journal of Formal Logic-

5—3)50.)ff[- 5'?ff8

"

"

S

Fine- 5'?(a

K8 Fine8 An ascending chain of

( logics8 Theoria- ([355[.550- 5'?(8

"

"

S

Fine- 5'?(b

K8 Fine8 An incomplete logic containing

(8 Theoria- ([3ff—.ff'- 5'?(8

"

"

K

Fine- 5'?(c

K8 Fine8 Logics containing

(- part I8 Journal of Symbolic Logic- —'3ffff'.

ff—?- 5'?(8

"

"

Fine- 5'?)a

K8 Fine8 Normal forms in modal logic8 Notre Dame Journal of Formal

Logic- 503—5.(ff- 5'?)8

5?ff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Fine- 5'?)b

K8 Fine8 Some connections between elementary and modal logic8

In

S8 Kanger- editor- Proceedings of the Third Scandinavian Logic Symposium- pages

5).—58 North2Holland- Amsterdam- 5'?)8

"

"

K

Fine- 5'fl)

K8 Fine8 Logics containing

(- part II8 Journal of Symbolic Logic- )[305'.

0)5- 5'fl)8

"

"

Fischer2Servi- 5'??

G8 Fischer2Servi8 On modal logics with an intuitionistic base8 Stu.

dia Logica- —035(5.5('- 5'??8

"

"

Fischer2Servi- 5'fl[

G8 Fischer2Servi8 Semantics for a class of intuitionistic modal cal2

culi8 In M8 L8 Dalla Chiara- editor- Italian Studies in the Philosophy of Science- pages

)'.?ff8 Reidel- Dordrecht- 5'fl[8

"

"

Fischer2Servi- 5'fl(

G8 Fischer2Servi8 Axiomatizations for some intuitionistic modal

logics8 Rend- Sem- Mat- Univers- Polit-- (ff35?'.5'(- 5'fl(8

"

"

Fitting- 5'fl—

M8 Fitting8 Proof Methods for Modal and Intuitionistic Logics8 Reidel-

Dordrecht- 5'fl—8

"

"

Font- 5'fl(

J8 Font8

Implication and deduction in some intuitionistic modal logics8

Reports on Mathematical logic- 5?3ff?.—fl- 5'fl(8

"

"

Font- 5'fl0

J8 Font8 Modality and possibility in some intuitionistic modal logics8 Notre

Dame Journal of Formal Logic- ff?3)——.)(0- 5'fl08

"

"

Friedman- 5'?)

H8 Friedman8 One hundred and two problems in mathematical logic8

Journal of Symbolic Logic- ([355—.5—[- 5'?)8

"

"

Fuhrmann- 5'fl'

A8 Fuhrmann8 Models for relevant modal logics8 Studia Logica-

('3)[ff.)5(- 5'fl'8

"

"

Gabbay and de Jongh- 5'?(

D8M8 Gabbay and D8H8J8 de Jongh8 A sequence of decid2

able :nitely axiomatizable intermediate logics with the disjunction property8 Journal

of Symbolic Logic- —'30?.?fl- 5'?(8

"

"

Gabbay et al-- 5''(

D8 Gabbay- I8 Hodkinson- and M8 Reynolds8 Temporal Logic.

Mathematical Foundations and Computational Aspects: Volume "8 Oxford Univer2

sity Press- 5''(8

"

"

Gabbay- 5'?[

D8M8 Gabbay8 The decidability of the Kreisel.Putnam system8 Journal

of Symbolic Logic- —)3(—5.(—0- 5'?[8

"

"

Gabbay- 5'?5

D8M8 Gabbay8 On decidable- :nitely axiomatizable modal and tense

logics without the :nite model property8 I- II8 Israel Journal of Mathematics- 5[3(?fl.

(')- ('0.)[—- 5'?58

"

"

Gabbay- 5'?ff

D8M8 Gabbay8 Craig6s interpolation theorem for modal logics8

In

W8 Hodges- editor- Proceedings of logic conference: London "5—?- volume ff)) of Lec.

ture Notes in Mathematics- pages 555.5ff?8 Springer2Verlag- Berlin- 5'?ff8

"

"

Gabbay- 5'?)

D8M8 Gabbay8 Decidability results in non2classical logics8 Annals of

Mathematical Logic- fl3ff—?.ff')- 5'?)8

"

"

Gabbay- 5'?0

D8M8 Gabbay8 Investigations into Modal and Tense Logics: with Appli.

cations to Problems in Linguistics and Philosophy8 Reidel- Dordrecht- 5'?08

"

"

Gabbay- 5'fl5a

D8M8 Gabbay8 An irreoexivity lemma with application to axiomatiza2

tions of conditions on linear frames8 In U8 Mfionnich- editor- Aspects of Philosophical

Logic- pages 0?.fl'8 Reidel- Dordrecht- 5'fl58

"

"

Gabbay- 5'fl5b

D8M8 Gabbay8 Semantical Investigations in Heyting"s Intuitionistic

Logic8 Reidel- Dordrecht- 5'fl58

"

"

Galanter- 5''[

G8I8 Galanter8 A continuum of intermediate logics which are maximal

among the logics having the intuitionistic disjunctionless fragment8 In Proceedings of

"?th USSR Conference for Mathematical Logic- page (5- Alma.Ata- 5''[8 ]Russian78

"

"

Garey and Johnson- 5'?'

M8R8 Garey and D8S8 Johnson8 Computers and intractabil.

ity- A guide to the theory of NP.completeness8 Freemann- San Franzisco- 5'?'8

"

"

Gargov and Passy- 5''[

G8 Gargov and S8 Passy8 A note on Boolean modal logic8 In

P8 Petkov- editor- Mathematical Logic- pages ff''.—['8 Plenum Press- 5''[8

"

"

Gargov et al-- 5'fl?

G8 Gargov- S8 Passy- and T8 Tinchev8 Modal environment for

Boolean speculations8 In D8 Skordev- editor- Mathematical Logic and its Applications-

pages ff)—.ff0—8 Plenum Press- 5'fl?8

ADVANCED MODAL LOGIC

5?—

"

"

Gentzen- 5'—(.—)

G8 Gentzen8 Untersuchungen ,uber das logische Schliessen8 Mathe.

matische Zeitschrift- —'35?0.ff5[- ([).(—5- 5'—(.—)8

"

"

Ghilardi and Meloni- 5''?

S8 Ghilardi and G8 Meloni8 Constructive canonicity in non2

classical logics8 Annals of Pure and Applied Logic- 5''?8 To appear8

"

"

Ghilardi and Zawadowski- 5'')

S8 Ghilardi and M8 Zawadowski8 Unde:nability of

propositional quanti:ers in modal system

(8 Studia Logica- ))3ff)'.ff?5- 5'')8

S

"

"

Ghilardi- 5'')

S8 Ghilardi8 An algebraic theory of normal forms8 Annals of Pure and

Applied Logic- ?535fl'.ff()- 5'')8

"

"

Gfiodel- 5'—ff

K8 Gfiodel8 Zum intuitionistischen Aussagenkalkfiul8 Anzeiger der Akademie

der Wissenschaften in Wien- 0'30).00- 5'—ff8

"

"

Gfiodel- 5'——

K8 Gfiodel8 Eine Interpretation des intuitionistischen Aussagenkalkfiuls8

Ergebnisse eines mathematischen Kol loquiums- (3—'.([- 5'——8

"

"

Goldblatt and Thomason- 5'?(

R8I8 Goldblatt and S8K8 Thomason8 Axiomatic classes

in propositional modal logic8 In J8 Crossley- editor- Algebraic Logic: Lecture Notes in

Mathematics vol- ()?- pages 50—.5?—8 Springer- Berlin- 5'?(8

"

"

Goldblatt- 5'?0a

R8I8 Goldblatt8 Metamathematics of modal logic- Part I8 Reports on

Mathematical Logic- 03(5.?fl- 5'?08

"

"

Goldblatt- 5'?0b

R8I8 Goldblatt8 Metamathematics of modal logic- Part II8 Reports

on Mathematical Logic- ?3ff5.)ff- 5'?08

"

"

Goldblatt- 5'fl?

R8I8 Goldblatt8 Logics of Time and Computation8 Number ? in CSLI

Lecture Notes- Stanford8 CSLI- 5'fl?8

"

"

Goldblatt- 5'fl'

R8I8 Goldblatt8 Varieties of complex algebras8 Annals of Pure and

Applied Logic- —fl35?—.ff(5- 5'fl'8

"

"

Goldblatt- 5'')

R8I8 Goldblatt8 Elementary generation and canonicity for varieties of

boolean algebras with operators8 Algebra Universalis- —(3))5.0[?- 5'')8

"

"

Goranko and Gargov- 5''—

V8 Goranko and G8 Gargov8 Modal logic with names8 Jour.

nal of Philosophical Logic- ffff30[?.0—0- 5''—8

"

"

Goranko and Passy- 5''ff

V8 Goranko and S8 Passy8 Using the universal modality3

Gains and questions8 Journal of Logic and Computation- ff3).—[- 5''ff8

"

"

Goranko- 5''[a

V8 Goranko8 Completeness and incompleteness in the bimodal base

L

R,

R

'

]

78 In P8 Petkov- editor- Mathematical Logic- pages —55.—ff08 Plenum Press-

5''[8

"

"

Goranko- 5''[b

V8 Goranko8 Modal de:nability in enriched languages8 Notre Dame

Journal of Formal Logic- —53fl5.5[)- 5''[8

"

"

Gore- 5''(

R8 Gore8 Cut2free sequent and tableau systems for propositional Diodorian

modal logics8 Studia Logica- )—3(——.()fl- 5''(8

"

"

Grefe- 5''(

C8 Grefe8 Modale Logiken funktionaler Frames8 Master6s thesis- Depart2

ment of Mathematics- Freie Universitfiat Berlin- 5''(8

"

"

Grefe- 5''?

C8 Grefe8 Fischer Servi6s intuitionistic modal logic has the :nite model

property8 In M8 Kracht- M8 De Rijke- H8 Wansing- and M8 Zakharyaschev- editors-

Advances in Modal Logic8 CSLI- Stanford- 5''?8

"

"

Halpern and Moses- 5''ff

J8 Halpern and Yo8 Moses8 A guide to completeness and

complexity for modal logics of knowledge and belief8 Arti8cial Intel ligence- )(3—5'.

—?'- 5''ff8

"

"

Harrop- 5')fl

R8 Harrop8 On the existence of :nite models and decision procedures for

propositional calculi8 Proceedings of the Cambridge Philosophical Society- )(35.5—-

5')fl8

"

"

Hemaspaandra- 5''0

E8 Hemaspaandra8 The price of universality8 Notre Dame Journal

of Formal Logic- —?35?(.ff[—- 5''08

"

"

Hosoi and Ono- 5'?—

T8 Hosoi and H8 Ono8 Intermediate propositional logics ]A sur2

vey78 Journal of Tsuda Col lege- )30?.flff- 5'?—8

"

"

Hosoi- 5'0?

T8 Hosoi8 On intermediate logics8 Journal of the Faculty of Science:

University of Tokyo- 5(3ff'—.—5ff- 5'0?8

"

"

Hughes and Cresswell- 5'fl(

G8E8 Hughes and M8J8 Cresswell8 A Companion to Modal

Logic8 Methuen- London- 5'fl(8

5?(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Humberstone- 5'fl—

I8L8 Humberstone8

Inaccessible worlds8 Notre Dame Journal of

Formal Logic- ff(3—(0.—)ff- 5'fl—8

"

"

Isard- 5'??

S8 Isard8 A :nitely axiomatizable undecidable extension of

8 Theoria-

K

(—35').ff[ff- 5'??8

"

"

Janiczak- 5')—

A8 Janiczak8 Undecidability of some simple formalized theories8 Fun.

damenta Mathematicae- ([35—5.5—'- 5')—8

"

"

Jankov- 5'0—

V8A8 Jankov8 The relationship between deducibility in the intuitionistic

propositional calculus and :nite implicational structures8 Soviet Mathematics Dok.

lady- (35ff[—.5ff[(- 5'0—8

"

"

Jankov- 5'0fla

V8A8 Jankov8 The calculus of the weak 1law of excluded middle98 Math.

ematics of the USSR: Izvestiya- ff3''?.5[[(- 5'0fl8

"

"

Jankov- 5'0flb

V8A8 Jankov8 The construction of a sequence of strongly independent su2

perintuitionistic propositional calculi8 Soviet Mathematics Doklady- '3fl[0.fl[?- 5'0fl8

"

"

Jankov- 5'0'

V8A8 Jankov8 Conjunctively indecomposable formulas in propositional

calculi8 Mathematics of the USSR: Izvestiya- —35?.—)- 5'0'8

"

"

JaΦskowski- 5'—0

S8 JaΦskowski8 Recherches sur le syst⊆eme de la logique intuitioniste8 In

Actes Du Congr0es Intern- De Phil- Scienti8que- VI- Phil- Des Mathffematiques: Act-

Sc- Et Ind fl5fl: Paris- pages )fl.05- 5'—08

"

"

Jipsen and Rose- 5''—

P8 Jipsen and H8 Rose8 Varieties of Lattices8 5''—8

"

"

JΦonsson and Tarski- 5')5

B8 JΦonsson and A8 Tarski8 Boolean algebras with operators8

I8 American Journal of Mathematics- ?—3fl'5.'—'- 5')58

"

"

JΦonsson- 5''(

B8 JΦonsson8 On the canonicity of Sahlqvist identities8 Studia Logica-

)—3(?—.('5- 5''(8

"

"

Kashima- 5''(

R8 Kashima8 Cut2free sequent calculi for some tense logics8 Studia

Logica- )—355'.5—0- 5''(8

"

"

Kirk- 5'flff

R8E8 Kirk8 A result on propositional logics having the disjunction property8

Notre Dame Journal of Formal Logic- ff—3?5.?(- 5'flff8

"

"

Kleene- 5'()

S8 Kleene8 On the interpretation of intuitionistic number theory8 Journal

of Symbolic Logic- 5[35['.5ff(- 5'()8

"

"

Kleyman- 5'fl(

Yu8G8 Kleyman8 Some questions in the theory of varieties of groups8

Mathematics of the USSR: Izvestiya- ffff3——.0)- 5'fl(8

"

"

Koppelberg- 5'flfl

S8 Koppelberg8 General theory of Boolean algebras8

In J8 Monk-

editor- Handbook of Boolean Algebras- volume 58 North2Holland- Amsterdam- 5'flfl8

"

"

:

Kozen- 5'fl—

D8 Kozen8 Results on the propositional

2calculus8 Theoretical Computer

Science- ff?3———.—)(- 5'fl—8

"

"

Kozen- 5'flfl

D8 Kozen8 A :nite model theorem for the propositional

2calculus8 Studia

:

Logica- (?3ff—(.ff(5- 5'flfl8

"

"

Kracht and Wolter- 5''5

M8 Kracht and F8 Wolter8 Properties of independently ax2

iomatizable bimodal logics8 Journal of Symbolic Logic- )035(0'.5(fl)- 5''58

"

"

Kracht and Wolter- 5''?a

M8 Kracht and F8 Wolter8 Normal monomodal logics can

simulate all others8 Journal of Symbolic Logic- 5''?8 To appear8

"

"

Kracht and Wolter- 5''?b

M8 Kracht and F8 Wolter8 Simulation and transfer results

in modal logic3 A survey8 Studia Logica- 5''?8 To appear8

"

"

Kracht- 5''[

M8 Kracht8 An almost general splitting theorem for modal logic8 Studia

Logica- ('3()).(?[- 5''[8

"

"

Kracht- 5''ff

M8 Kracht8 Even more about the lattice of tense logics8 Archive of

Mathematical Logic- —53ff(—.—)?- 5''ff8

"

"

Kracht- 5''—

M8 Kracht8 How completeness and correspondence theory got married8

In M8 de Rijke- editor- Diamonds and Defaults- pages 5?).ff5(8 Kluwer Academic

Publishers- 5''—8

"

"

Kracht- 5''0

M8 Kracht8 Tools and techniques in modal logic8 Habilitationsschrift- FU

Berlin- 5''08

"

"

Kreisel and Putnam- 5')?

G8 Kreisel and H8 Putnam8 Eine Unableitbarkeitsbeweis2

methode ffiur den intuitionistischen Aussagenkalkfiul8 Zeitschrift ffiur Mathematische

Logik und Grund lagen der Mathematik- —3?(.?fl- 5')?8

ADVANCED MODAL LOGIC

5?)

"

"

Kruskal- 5'0[

J8 B8 Kruskal8 Well2quasi2ordering- the tree theorem and Vazsonyi6s

conjecture8 Transactions of the American Mathematical Society- ')3ff5[.ffff)- 5'0[8

"

"

Kuznetsov and Gerchiu- 5'?[

A8V8 Kuznetsov and V8Ya8 Gerchiu8 Superintuitionistic

logics and the :nite approximability8 Soviet Mathematics Doklady- 553505(.505'-

5'?[8

"

"

Kuznetsov- 5'0—

A8V8 Kuznetsov8 Undecidability of general problems of completeness-

decidability and equivalence for propositional calculi8 Algebra and Logic- ff3(?.00-

5'0—8 ]Russian78

"

"

Kuznetsov- 5'?5

A8V8 Kuznetsov8 Some properties of the structure of varieties of

pseudo2Boolean algebras8

In Proceedings of the XIth USSR Algebraic Col loquium-

pages ff)).ff)0- Kishinev- 5'?58 ]Russian78

"

"

Kuznetsov- 5'?ff

A8V8 Kuznetsov8 The decidability of certain superintuitionistic cal2

culi8 In Proceedings of the IInd USSR Conference on Mathematical Logic- Moscow-

5'?ff8 ]Russian78

"

"

Kuznetsov- 5'?)

A8V8 Kuznetsov8 On superintuitionistic logics8 In Proceedings of the

International Congress of Mathematicians- pages ff(—.ff('- Vancouver- 5'?)8

"

"

Kuznetsov- 5'?'

A8V8 Kuznetsov8

Tools for detecting non2derivability or non2

expressibility8 In V8A8 Smirnov- editor- Logical Inference- Proceedings of the USSR

Symposium on the Theory of Logical Inference- pages ).ff—8 Nauka- Moscow- 5'?'8

]Russian78

"

"

Kuznetsov- 5'fl)

A8V8 Kuznetsov8 Proof2intuitionistic propositional calculus8 Doklady

Academii Nauk SSSR- fffl—3ff?.—[- 5'fl)8 ]Russian78

"

"

Ladner- 5'??

R8E8 Ladner8 The computational complexity of provability in systems of

modal logic8 SIAM Journal on Computing- 03(0?.(fl[- 5'??8

"

"

Lemmon and Scott- 5'??

E8J8 Lemmon and D8S8 Scott8 An Introduction to Modal

Logic8 Oxford- Blackwell- 5'??8

"

"

Lemmon- 5'00a

E8J8 Lemmon8 Algebraic semantics for modal logic8 I8 Journal of

Symbolic Logic- —53(0.0)- 5'008

"

"

Lemmon- 5'00b

E8J8 Lemmon8 Algebraic semantics for modal logic8 II8 Journal of

Symbolic Logic- —535'5.ff5fl- 5'008

"

"

Lemmon- 5'00c

E8J8 Lemmon8 A note on HalldΦen2incompleteness8 Notre Dame Journal

of Formal Logic- ?3ff'0.—[[- 5'008

"

"

Levin- 5'0'

V8A8 Levin8 Some syntactic theorems on the calculus of :nite problems of

Yu8T8 Medvedev8 Soviet Mathematics Doklady- 5[3ffflfl.ff'[- 5'0'8

"

"

Lewis- 5'5fl

C8I8 Lewis8 A Survey of Symbolic Logic8 University of California Press-

Berkeley- 5'5fl8

"

"

Lewis- 5'?(

D8 Lewis8 Intensional logics without iterative axioms8 Journal of Philo.

sophical logic- —3()?.(00- 5'?(8

"

"

Lincoln et al-- 5''ff

P8D8 Lincoln- J8 Mitchell- A8 Scedrov- and N8 Shankar8 Decision

problems for propositional linear logic8 Annals of Pure and Applied Logic- )03ff—'.—55-

5''ff8

"

"

 Lukasiewicz- 5')ff

J8  Lukasiewicz8 On the intuitionistic theory of deduction8 Indaga.

tiones Mathematicae- 5(3ff[ff.ff5ff- 5')ff8

"

"

Luppi- 5''0

C8 Luppi8 On the interpolation property of some intuitionistic modal

logics8 Archive for Mathematical Logic- —)35?—.5fl'- 5''08

"

"

Makinson- 5'?5

D8C8 Makinson8 Some embedding theorems for modal logic8 Notre

Dame Journal of Formal Logic- 5ff3ff)ff.ff)(- 5'?58

"

"

Maksimova and Rybakov- 5'?(

L8L8 Maksimova and V8V8 Rybakov8 Lattices of modal

logics8 Algebra and Logic- 5—35[).5ffff- 5'?(8

"

"

Maksimova et al-- 5'?'

L8L8 Maksimova- V8B8 Shehtman- and D8P8 Skvortsov8 The

impossibility of a :nite axiomatization of Medvedev6s logic of :nitary problems8 Soviet

Mathematics Doklady- ff[3—'(.—'fl- 5'?'8

"

"

Maksimova- 5'?ff

L8L8 Maksimova8 Pretabular superintuitionistic logics8 Algebra and

Logic- 553—[fl.—5(- 5'?ff8

"

"

Maksimova- 5'?)a

L8L8 Maksimova8 Modal logics of :nite slices8 Algebra and Logic-

5(35flfl.5'?- 5'?)8

5?0

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Maksimova- 5'?)b

L8L8 Maksimova8 Pretabular extensions of Lewis

(8 Algebra and

S

Logic- 5(350.——- 5'?)8

"

"

Maksimova- 5'?'

L8L8 Maksimova8 Interpolation theorems in modal logic and amal2

gamable varieties of topological Boolean algebras8 Algebra and Logic- 5fl3—(fl.—?[-

5'?'8

"

"

Maksimova- 5'flffa

L8L8 Maksimova8 Failure of the interpolation property in modal

companions of Dummett6s logic8 Algebra and Logic- ff530'[.0'(- 5'flff8

"

"

Maksimova- 5'flffb

L8L8 Maksimova8 Lyndon6s interpolation theorem in modal logics8

In Mathematical Logic and Algorithm Theory- pages ().))8 Institute of Mathematics-

Novosibirsk- 5'flff8 ]Russian78

"

"

Maksimova- 5'fl(

L8L8 Maksimova8 On the number of maximal intermediate logics

having the disjunction property8

In Proceedings of the —th USSR Conference for

Mathematical Logic- page ')8 Institute of Mathematics- Novosibirsk- 5'fl(8 ]Russian78

"

"

Maksimova- 5'fl0

L8L8 Maksimova8 On maximal intermediate logics with the disjunc2

tion property8 Studia Logica- ()30'.?)- 5'fl08

"

"

Maksimova- 5'fl?

L8L8 Maksimova8 On the interpolation in normal modal logics8 Non.

classical Logics: Studies in Mathematics- 'fl3([.)0- 5'fl?8 ]Russian78

"

"

Maksimova- 5'fl'

L8L8 Maksimova8 A continuum of normal extensions of the modal

provability logic with the interpolation property8 Sibirskij Matemati[ceskij

Zurnal-

[

—[35ffff.5—5- 5'fl'8 ]Russian78

"

"

Maksimova- 5''ff

L8L8 Maksimova8 De:nability and interpolation in classical modal

logics8 Contemporary Mathematics- 5—53)fl—.)''- 5''ff8

"

"

Maksimova- 5'')

L8L8 Maksimova8 On variable separation in modal and superintu2

itionistic logics8 Studia Logica- ))3''.55ff- 5'')8

"

"

Mal6cev- 5'?[

A8I8 Mal6cev8 Algorithms and Recursive Functions8 Wolters2Noordho4-

Groningen- 5'?[8

"

"

Mal6cev- 5'?—

A8I8 Mal6cev8 Algebraic Systems8 Springer2Verlag- Berlin2Heidelberg-

5'?—8

"

"

Mardaev- 5'fl(

S8I8 Mardaev8 The number of prelocally tabular superintuitionistic

propositional logics8 Algebra and Logic- ff—3)0.00- 5'fl(8

"

"

Marx- 5'')

M8 Marx8 Algebraic relativization and arrow logic8 PhD thesis- University

of Amsterdam- 5'')8

"

"

Masini- 5''ff

A8 Masini8 ff2sequent calculus3 a proof theory of modality8 Annals of

Pure and Applied Logic- )fl3ffff'.ff(0- 5''ff8

"

"

Matiyasevich- 5'0?

Y8V8 Matiyasevich8 Simple examples of undecidable associative

calculi8 Soviet Mathematics Doklady- fl3))).))?- 5'0?8

"

"

McKay- 5'0fl

C8G8 McKay8 The decidability of certain intermediate logics8 Journal of

Symbolic Logic- ——3ff)fl.ff0(- 5'0fl8

"

"

McKay- 5'?5

C8G8 McKay8 A class of decidable intermediate propositional logics8 Jour.

nal of Symbolic Logic- —035ff?.5fffl- 5'?58

"

"

McKenzie- 5'?ff

R8 McKenzie8 Equational bases and non2modular lattice varieties8

Transactions of the American Mathematical Society- 5?(35.(—- 5'?ff8

"

"

McKinsey and Tarski- 5'(0

J8C8C8 McKinsey and A8 Tarski8 On closed elements in

closure algebras8 Annals of Mathematics- (?35ffff.50ff- 5'(08

"

"

McKinsey and Tarski- 5'(fl

J8C8C8 McKinsey and A8 Tarski8 Some theorems about the

sentential calculi of Lewis and Heyting8 Journal of Symbolic Logic- 5—35.5)- 5'(fl8

"

"

McKinsey- 5'(5

J8C8C8 McKinsey8 A solution of the decision problem for the Lewis

systems

ff and

(- with an application to topology8 Journal of Symbolic Logic-

S

S

0355?.5—(- 5'(58

"

"

Medvedev- 5'0ff

Yu8T8 Medvedev8 Finite problems8 Soviet Mathematics Doklady-

—3ffff?.ff—[- 5'0ff8

"

"

Medvedev- 5'00

Yu8T8 Medvedev8 Interpretation of logical formulas by means of :nite

problems8 Soviet Mathematics Doklady- ?3fl)?.fl0[- 5'008

"

"

Meyer and van der Hoek- 5'')

J8 Meyer and W8 van der Hoek8 Epistemic Logic for

AI and Computer Science8 Cambridge University Press- 5'')8

"

"

Mikulas- 5'')

S8 Mikulas8 Taming Logics8 PhD thesis- University of Amsterdam- 5'')8

ADVANCED MODAL LOGIC

5??

"

"

Minari- 5'fl0

P8 Minari8 Intermediate logics with the same disjunctionless fragment as

intuitionistic logic8 Studia Logica- ()3ff[?.ffffff- 5'fl08

"

"

Montagna- 5'fl?

F8 Montagna8 Provability in :nite subtheories of PA and relative

interpretability3 a modal investigation8 Journal of Symbolic Logic- )ff3('(.)55- 5'fl?8

"

"

Morikawa- 5'fl'

O8 Morikawa8 Some modal logics based on three2valued logic8 Notre

Dame Journal of Formal Logic- —[35—[.5—?- 5'fl'8

"

"

,

I

Muravitskij- 5'fl5

A8Yu8 Muravitskij8 On :nite approximability of the calculus

and

non2modelability of some of its extensions8 Mathematical Notes- ff'3'[?.'50- 5'fl58

"

"

Nagle and Thomason- 5'fl)

M8C8 Nagle and S8K8 Thomason8 The extensions of the

modal logic

)8 Journal of Symbolic Logic- )[35[ff.5[fl- 5'fl)8

K

"

"

Nishimura- 5'0[

I8 Nishimura8 On formulas of one variable in intuitionistic proposi2

tional calculus8 Journal of Symbolic Logic- ff)3—ff?.——5- 5'0[8

"

"

Ono and Nakamura- 5'fl[

H8 Ono and A8 Nakamura8 On the size of refutation Kripke

models for some linear modal and tense logics8 Studia Logica- —'3—ff).———- 5'fl[8

"

"

Ono and Suzuki- 5'flfl

H8 Ono and N8 Suzuki8 Relations between intuitionistic modal

logics and intermediate predicate logics8 Reports on Mathematical Logic- ffff30).fl?-

5'flfl8

"

"

Ono- 5'?ff

H8 Ono8 Some results on the intermediate logics8 Publications of the Re.

search Institute for Mathematical Science: Kyoto University- fl355?.5—[- 5'?ff8

"

"

Ono- 5'??

H8 Ono8 On some intuitionistic modal logics8 Publications of the Research

Institute for Mathematical Science: Kyoto University- 5—3)).0?- 5'??8

"

"

Orlov- 5'fffl

I8E8 Orlov8 The calculus of compatibility of propositions8 Mathematics of

the USSR: Sbornik- —)3ff0—.fffl0- 5'fffl8 ]Russian78

"

"

Ostermann- 5'flfl

P8 Ostermann8 Many2valued modal propositional calculi8 Zeitschrift

fur mathematische Logik und Grund lagen der Mathematik- —(3—(—.—)(- 5'flfl8

"

"

Pigozzi- 5'?(

D8 Pigozzi8 The join of equational theories8 Col loquium Mathematicum-

—[35).ff)- 5'?(8

"

"

Pitts- 5''ff

A8M8 Pitts8 On an interpretation of second order quanti:cation in :rst

order intuitionistic propositional logic8 Journal of Symbolic Logic- )?3——.)ff- 5''ff8

"

"

Ponse et al-- 5''0

A8 Ponse- M8 de Rijke- and Y8 Venema8 Modal Logic and Process

Algebra8 CSLI Publications- Stanford- 5''08

"

"

Prior- 5')?

A8 Prior8 Time and Modality8 Clarendon Press- Oxford- 5')?8

"

"

Rabin- 5'0'

M8O8 Rabin8 Decidability of second order theories and automata on in:2

nite trees8 Transactions of the American Mathematical Society- 5(535.—)- 5'0'8

"

"

Rabin- 5'??

M8O8 Rabin8 Decidable theories8 In J8 Barwise- editor- Handbook of Math.

ematical Logic- pages )').0—[8 Elsevier- North2Holland- 5'??8

"

"

Rasiowa and Sikorski- 5'0—

H8 Rasiowa and R8 Sikorski8 The Mathematics of Meta.

mathematics8 Polish Scienti:c Publishers- 5'0—8

"

"

Rautenberg- 5'??

W8 Rautenberg8 Der Verband der normalen verzweigten Modal2

logiken8 Mathematische Zeitschrift- 5)035ff—.5([- 5'??8

"

"

Rautenberg- 5'?'

W8 Rautenberg8 Klassische und nichtklassische Aussagenlogik8

Vieweg- Braunschweig.Wiesbaden- 5'?'8

"

"

Rautenberg- 5'fl[

W8 Rautenberg8 Splitting lattices of logics8 Archiv ffiur Mathematis.

che Logik- ff[35)).5)'- 5'fl[8

"

"

Rautenberg- 5'fl—

W8 Rautenberg8 Modal tableau calculi and interpolation8 Journal

of Philosophical Logic- 5ff3([—.(ff—- 5'fl—8

"

"

Rieger- 5'('

L8 Rieger8 On the lattice of Brouwerian propositional logics8 Acta Uni.

versitatis Carolinae- Mathematica et Physica- 5fl'- 5'('8

"

"

Rodenburg- 5'fl0

P8H8 Rodenburg8 Intuitionistic correspondence theory8 PhD thesis-

University of Amsterdam- 5'fl08

"

"

Rose- 5')—

G8F8 Rose8 Propositional calculus and realizability8 Transactions of the

American Mathematical Society- ?)35.5'- 5')—8

"

"

Rybakov- 5'??

V8V8 Rybakov8 Noncompact extensions of the logic

(8 Algebra and

S

Logic- 503—ff5.——(- 5'??8

"

"

Rybakov- 5'?fl

V8V8 Rybakov8 Modal logics with LM2axioms8 Algebra and Logic-

5?3—[ff.—5[- 5'?fl8

5?fl

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Rybakov- 5'fl(a

V8V8 Rybakov8 Admissible rules for logics containing

(

—8 Siberian

S

.

Mathematical Journal- ff)3?').?'fl- 5'fl(8

"

"

Rybakov- 5'fl(b

V8V8 Rybakov8 A criterion for admissibility of rules in the modal

system

( and intuitionistic logic8 Algebra and Logic- ff—3—0'.—fl(- 5'fl(8

S

"

"

Rybakov- 5'fl?

V8V8 Rybakov8 The decidability of admissibility of inference rules in

the modal system

and intuitionistic logic8 Mathematics of the USSR: Izvestiya-

Grz

fffl3)fl'.0[fl- 5'fl?8

"

"

Rybakov- 5'fl'

V8V8 Rybakov8 Admissibility of inference rules in the modal system

8

G

Mathematical Logic and Algorithmical Problems: Mathematical Institute: Novosibirsk-

5ff35ff[.5—fl- 5'fl'8 ]Russian78

"

"

Rybakov- 5''—

V8V8 Rybakov8 Rules of inference with parameters for intuitionistic

logic8 Journal of Symbolic Logic- )fl35fl[—.5fl—(- 5''—8

"

"

Rybakov- 5''(

V8V8 Rybakov8 Criteria for admissibility of inference rules8 Modal and

intermediate logics with the branching property8 Studia Logica- )—3ff[—.ffff0- 5''(8

"

"

Rybakov- 5'')

V8V8 Rybakov8 Hereditarily structurally complete modal logics8 Journal

of Symbolic Logic- 0[3ff00.ffflfl- 5'')8

"

"

Sahlqvist- 5'?)

H8 Sahlqvist8 Completeness and correspondence in the :rst and sec2

ond order semantics for modal logic8 In S8 Kanger- editor- Proceedings of the Third

Scandinavian Logic Symposium- pages 55[.5(—8 North2Holland- Amsterdam- 5'?)8

"

"

Sambin and Vaccaro- 5'fl'

G8 Sambin and V8 Vaccaro8

A topological proof of

Sahlqvist6s theorem8 Journal of Symbolic Logic- )(3''ff.'''- 5'fl'8

"

"

Sasaki- 5''ff

K8 Sasaki8 The disjunction property of the logics with axioms of only one

variable8 Bul letin of the Section of Logic- ff53([.(0- 5''ff8

"

"

S

Scroggs- 5')5

S8J8 Scroggs8 Extensions of the Lewis system

)8 Journal of Symbolic

Logic- 50355ff.5ff[- 5')58

"

"

Segerberg- 5'0?

K8 Segerberg8 Some modal logics based on three valued logic8 Theoria-

——3)—.?5- 5'0?8

"

"

Segerberg- 5'?[

K8 Segerberg8 Modal logics with linear alternative relations8 Theoria-

—03—[5.—ffff- 5'?[8

"

"

Segerberg- 5'?5

K8 Segerberg8 An essay in classical modal logic8 Philosophical Studies:

Uppsala- 5—- 5'?58

"

"

S

.

Segerberg- 5'?)

K8 Segerberg8 That all extensions of

(

— are normal8 In S8 Kanger- ed2

itor- Proceedings of the Third Scandinavian Logic Symposium- pages 5'(.5'08 North2

Holland- Amsterdam- 5'?)8

"

"

Segerberg- 5'fl0

K8 Segerberg8 Modal logics with functional alternative relations8 Notre

Dame Journal of Formal Logic- ff?3)[(.)ffff- 5'fl08

"

"

Segerberg- 5'fl'

K8 Segerberg8 Von Wright6s tense logic8 In P8 Schilpp and L8 Hahn-

editors- The Philosophy of Georg Henrik von Wright- pages 0[—.0—)8 La Salle- IL3

Open Court- 5'fl'8

"

"

Shavrukov- 5''5

V8Yu8 Shavrukov8 On two extensions of the provability logic

8

GL

Mathematics of the USSR: Sbornik- 0'3ff)).ff?[- 5''58

"

"

Shavrukov- 5''—

V8Yu8 Shavrukov8 Subalgebras of diagonalizable algebras of theories

containing arithmetic8 Dissertationes Mathematicae 6Rozprawy Matematyczne: Pol.

ska Akademia Nauk: Instytut Matematyczny]: Warszawa- —ff—- 5''—8

"

"

Shehtman- 5'??

V8B8 Shehtman8 On incomplete propositional logics8 Soviet Mathe.

matics Doklady- 5fl3'fl).'fl'- 5'??8

"

"

Shehtman- 5'?fla

V8B8 Shehtman8 Rieger.Nishimura lattices8 Soviet Mathematics

Doklady- 5'35[5(.5[5fl- 5'?fl8

"

"

Shehtman- 5'?flb

V8B8 Shehtman8 An undecidable superintuitionistic propositional

calculus8 Soviet Mathematics Doklady- 5'30)0.00[- 5'?fl8

"

"

Shehtman- 5'?'

V8B8 Shehtman8 Kripke type semantics for propositional modal logics

with the intuitionistic base8 In V8A8 Smirnov- editor- Modal and Tense Logics- pages

5[fl.55ff8 Institute of Philosophy- USSR Academy of Sciences- 5'?'8 ]Russian78

"

"

Shehtman- 5'fl[

V8B8 Shehtman8 Topological models of propositional logics8 Semiotics

and Information Science- 5)3?(.'fl- 5'fl[8 ]Russian78

ADVANCED MODAL LOGIC

5?'

"

"

Shehtman- 5'flff

V8B8 Shehtman8 Undecidable propositional calculi8

In Problems of

Cybernetics- Nonclassical logics and their application- volume ?)- pages ?(.5508 USSR

Academy of Sciences- 5'flff8 ]Russian78

"

"

Shimura- 5''—

T8 Shimura8 Kripke completeness of some intermediate predicate logics

with the axiom of constant domain and a variant of canonical formulas8 Studia Logica-

)ff3ff—.([- 5''—8

"

"

Shimura- 5'')

T8 Shimura8 On completeness of intermediate predicate logics with

respect to Kripke semantics8 Bul letin of the Section of Logic- ff(3(5.()- 5'')8

"

"

Shum- 5'fl)

A8A8 Shum8 Relative varieties of algebraic systems- and propositional

calculi8 Soviet Mathematics Doklady- —53('ff.(')- 5'fl)8

"

"

Simpson- 5''(

A8K8 Simpson8 The proof theory and semantics of intuitionistic modal

logic8 PhD thesis- University of Edinburgh- 5''(8

"

"

SmoryΦnski- 5'?—

C8 SmoryΦnski8

Investigations of Intuitionistic Formal Systems by

means of Kripke Frames8 PhD thesis- University of Illinois- 5'?—8

"

"

SmoryΦnski- 5'?fl

C8 SmoryΦnski8 Beth6s theorem and self2referential sentences8 In Logic

Col loquium ——- pages ff)—.ff058 North2Holland- Amsterdam- 5'?fl8

"

"

SmoryΦnski- 5'fl)

C8 SmoryΦnski8 Self.reference and Modal Logic8 Springer Verlag- Hei2

delberg ! New York- 5'fl)8

"

"

Sobolev- 5'??a

S8K8 Sobolev8 On :nite2dimensional superintuitionistic logics8 Mathe.

matics of the USSR: Izvestiya- 553'['.'—)- 5'??8

"

"

Sobolev- 5'??b

S8K8 Sobolev8 On the :nite approximability of superintuitionistic logics8

Mathematics of the USSR: Sbornik- —53ff)?.ff0fl- 5'??8

"

"

Solovay- 5'?0

R8 Solovay8 Provability interpretations of modal logic8 Israel Journal of

Mathematics- ff)3fffl?.—[(- 5'?08

"

"

Sotirov- 5'fl(

V8H8 Sotirov8 Modal theories with intuitionistic logic8

In Proceedings

of the Conference on Mathematical Logic: So8a: "57?- pages 5—'.5?58 Bulgarian

Academy of Sciences- 5'fl(8

"

"

Spaan- 5''—

E8 Spaan8 Complexity of Modal Logics8 PhD thesis- Department of Math2

ematics and Computer Science- University of Amsterdam- 5''—8

"

"

Statman- 5'?'

R8 Statman8 Intuitionistic propositional logic is polynomial2space com2

plete8 Theoretical Computer Science- '30?.?ff- 5'?'8

"

"

Surendonk- 5''0

T8 Surendonk8 Canonicity of intensional logics without iterative ax2

ioms8 Journal of Philosophical Logic- 5''08 To appear8

"

"

Suzuki- 5''[

N8 Suzuki8 An algebraic approach to intuitionistic modal logics in con2

nection with intermediate predicate logics8 Studia Logica- (fl35(5.5))- 5''[8

"

"

Tarski- 5')(

A8 Tarski8 Contributions to the theory of models I- II8

Indagationes

Mathematicae- 503)?ff.)flfl- 5')(8

"

"

Thomason- 5'?ff

S8 K8 Thomason8 Noncompactness in propositional modal logic8 Jour.

nal of Symbolic Logic- —?3?50.?ff[- 5'?ff8

"

"

Thomason- 5'?(a

S8 K8 Thomason8 An incompleteness theorem in modal logic8 Theo.

ria- ([3—[.—(- 5'?(8

"

"

Thomason- 5'?(b

S8 K8 Thomason8 Reduction of tense logic to modal logic I8 Journal

of Symbolic Logic- —'3)('.))5- 5'?(8

"

"

Thomason- 5'?)a

S8 K8 Thomason8 The logical consequence relation of propositional

tense logic8 Zeitschrift ffiur mathematische Logik und Grund lagen der Mathematik-

ff53ff'.([- 5'?)8

"

"

Thomason- 5'?)b

S8 K8 Thomason8 Reduction of second2order logic to modal logic8

Zeitschrift ffiur mathematische Logik und Grund lagen der Mathematik- ff535[?.55(-

5'?)8

"

"

Thomason- 5'?)c

S8 K8 Thomason8 Reduction of tense logic to modal logic II8 Theoria-

(535)(.50'- 5'?)8

"

"

Thomason- 5'fl[

S8 K8 Thomason8

Independent propositional modal logics8 Studia

Logica- —'35(—.5((- 5'fl[8

"

"

Thomason- 5'flff

S8 K8 Thomason8 Undecidability of the completeness problem of

modal logic8

In Universal Algebra and Applications: Banach Center Publications-

volume '- pages —(5.—()- Warsaw- 5'flff8 PNW.Polish Scienti:c Publishers8

5fl[

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Tseitin- 5')fl

G8S8 Tseitin8 Associative calculus with unsolvable equivalence problem8

Proceedings of the Mathematical Steklov Institute of the USSR Academy of Sciences-

)ff35?ff.5fl'- 5')fl8 Translation3 American Mathematical Society8 Translations8 Series

ff8 '(3?—.'ff8

"

"

Tsytkin- 5'?fl

A8I8 Tsytkin8 On structurally complete superintuitionistic logics8 Soviet

Mathematics Doklady- 5'3fl50.fl5'- 5'?fl8

"

"

Tsytkin- 5'fl?

A8I8 Tsytkin8 Structurally complete superintuitionistic logics and prim2

itive varieties of pseudo2Boolean algebras8 Mathematical Studies- 'fl35—(.5)5- 5'fl?8

]Russian78

"

"

,

Umezawa- 5'))

T8 Umezawa8

Uber die Zwischensysteme der Aussagenlogik8 Nagoya

Mathematical Journal- '35fl5.5fl'- 5'))8

"

"

Umezawa- 5')'

T8 Umezawa8 On intermediate propositional logics8 Journal of Sym.

bolic Logic- ff(3ff[.—0- 5')'8

"

"

Urquhart- 5'?(

A8 Urquhart8 Implicational formulas in intuitionistic logic8 Journal of

Symbolic Logic- —'3005.00(- 5'?(8

"

"

Urquhart- 5'fl(

A8 Urquhart8 The undecidability of entailment and relevant implica2

tion8 Journal of Symobolic Logic- ('35[)'.5[?—- 5'fl(8

"

"

Vakarelov- 5'fl5

D8 Vakarelov8 Intuitionistic modal logics incompatible with the law of

excluded middle8 Studia Logica- ([35[—.555- 5'fl58

"

"

Vakarelov- 5'fl)

D8 Vakarelov8 An application of the Rieger.Nishimura formulas to the

intuitionistic modal logics8 Studia Logica- ((3?'.fl)- 5'fl)8

"

"

van Benthem and Blok- 5'?fl

J8A8F8K8 van Benthem and W8J8 Blok8 Transitivity fol2

lows from Dummett6s axiom8 Theoria- ((355?.55fl- 5'?fl8

"

"

van Benthem and Humberstone- 5'fl—

J8A8F8K8 van Benthem and I8L8 Humberstone8

HalldΦen2completeness by gluing Kripke frames8 Notre Dame Journal of Formal Logic-

ff(3(ff0.(—[- 5'fl—8

"

"

van Benthem- 5'?0

J8A8F8K8 van Benthem8 Modal reduction principles8 Journal of

Symbolic Logic- (53—[5.—5ff- 5'?08

"

"

van Benthem- 5'?'

J8A8F8K8 van Benthem8 Syntactic aspects of modal incompleteness

theorems8 Theoria- ()30—.??- 5'?'8

"

"

van Benthem- 5'fl[

J8A8F8K8 van Benthem8 Some kinds of modal completeness8 Studia

Logica- —'35ff).5(5- 5'fl[8

"

"

van Benthem- 5'fl—

J8A8F8K8 van Benthem8 Modal Logic and Classical Logic8 Bibliopo2

lis- Napoli- 5'fl—8

"

"

van der Hoek- 5''ff

W8 van der Hoek8 Modalities for Reasoning about Know ledge and

Quantities8 PhD thesis- University of Amsterdam- 5''ff8

"

"

Venema- 5''5

Y8 Venema8 Many.Dimensional Modal Logics8 PhD thesis- Universiteit

van Amsterdam- 5''58

"

"

Visser- 5'')

A8 Visser8 A course in bimodal provability logic8 Annals of Pure and

Applied Logic- ?—355).5(ff- 5'')8

"

"

Visser- 5''0

A8 Visser8 Uniform interpolation and layered bisimulation8 In P8 Hayek-

editor- Gfiodel"5'- pages 5—'.50(8 Springer Verlag- 5''08

"

"

Walukiewicz- 5''—

I8 Walukiewicz8 A Complete Deduction system for the

.calculus8

:

PhD thesis- Warsaw- 5''—8

"

"

Walukiewicz- 5''0

I8 Walukiewicz8 A note on the completeness of Kozen6s axiomati2

zation of the propositional

2calculus8 Bul letin of Symbolic Logic- ff3—('.—00- 5''08

:

"

"

Wang- 5''ff

X8 Wang8 The McKinsey axiom is not compact8 Journal of Symbolic

Logic- )?35ff—[.5ff—fl- 5''ff8

"

"

Wansing- 5''(

H8 Wansing8 Sequent calculi for normal modal propositional logics8

Journal of Logic and Computation- (35ff).5(ff- 5''(8

"

"

Wansing- 5''0

H8 Wansing8 Proof Theory of Modal Logic8 Kluwer Academic Publish2

ers- 5''08

"

"

Whitman- 5'(—

P8 Whitman8 Splittings of a lattice8 American Journal of Mathematics-

0)35?'.5'0- 5'(—8

"

"

Wijesekera- 5''[

D8 Wijesekera8 Constructive modal logic I8 Annals of Pure and

Applied Logic- )[3ff?5.—[5- 5''[8

ADVANCED MODAL LOGIC

5fl5

"

"

Williamson- 5''(

T8 Williamson8 Non2genuine MacIntosh logics8 Journal of Philo.

sophical Logic- ff—3fl?.5[5- 5''(8

"

"

Wolter and Zakharyaschev- 5''?a

F8 Wolter and M8 Zakharyaschev8

Intuitionistic

modal logics as fragments of classical bimodal logics8 In E8 Orlowska- editor- Logic at

Work8 Kluwer Academic Publishers- 5''?8 In print8

"

"

Wolter and Zakharyaschev- 5''?b

F8 Wolter and M8 Zakharyaschev8 On the relation

between intuitionistic and classical modal logics8 Algebra and Logic- 5''?8 To appear8

"

"

Wolter- 5''—

F8 Wolter8 Lattices of Modal Logics8 PhD thesis- Freie Universitfiat Berlin-

5''—8 Parts of this paper will appear in Annals of Pure and Applied Logic under the

title 1The structure of lattices of subframe logics98

"

"

Wolter- 5''(a

F8 Wolter8 Solution to a problem of Goranko and Passy8 Journal of

Logic and Computation- (3ff5.ffff- 5''(8

"

"

Wolter- 5''(b

F8 Wolter8 What is the upper part of the lattice of bimodal logics"

Studia Logica- )—3ff—).ff(ff- 5''(8

"

"

Wolter- 5'')

F8 Wolter8 The :nite model property in tense logic8 Journal of Symbolic

Logic- 0[3?)?.??(- 5'')8

"

"

Wolter- 5''0a

F8 Wolter8 Completeness and decidability of tense logics closely related

to logics containing

(8 Journal of Symbolic Logic- 5''08 To appear8

K

"

"

Wolter- 5''0b

F8 Wolter8 A counterexample in tense logic8 Notre Dame Journal of

Formal Logic- —?350?.5?—- 5''08

"

"

Wolter- 5''0c

F8 Wolter8 Properties of tense logics8 Mathematical Logic Quarterly-

(ff3(fl5.)[[- 5''08

"

"

Wolter- 5''0d

F8 Wolter8 Tense logics without tense operators8 Mathematical Logic

Quarterly- (ff35().5?5- 5''08

"

"

Wolter- 5''?a

F8 Wolter8 All :nitely axiomatizable subframe logics containing CSM

are decidable8 Archive for Mathematical Logic- 5''?8 To appear8

"

"

Wolter- 5''?b

F8 Wolter8 Fusions of modal logics revisited8

In M8 Kracht- M8 De

Rijke- H8 Wansing- and M8 Zakharyaschev- editors- Advances in Modal Logic8 CSLI-

Stanford- 5''?8

"

"

Wolter- 5''?c

F8 Wolter8 A note on atoms in polymodal algebras8 Algebra Universalis-

5''?8 To appear8

"

"

Wolter- 5''?d

F8 Wolter8 A note on the interpolation property in tense logic8 Journal

of Philosophical Logic- 5''?8 To appear8

"

"

Wolter- 5''?e

F8 Wolter8 Superintuitionistic companions of classical modal logics8 Stu.

dia Logica- )fl3ffff'.ff)'- 5''?8

"

"

WroΦnski- 5'?—

A8 WroΦnski8 Intermediate logics and the disjunction property8 Reports

on Mathematical Logic- 53—'.)5- 5'?—8

"

"

WroΦnski- 5'?(

A8 WroΦnski8 Remarks on intermediate logics with axioms containing

only one variable8 Reports on Mathematical Logic- ff30—.?)- 5'?(8

"

"

WroΦnski- 5'fl'

A8 WroΦnski8 Su#cient condition of decidability for intermediate propo2

sitional logics8 In ASL Logic Col loquium: Berlin"75- 5'fl'8

"

"

Zakharyaschev and Alekseev- 5'')

M8 Zakharyaschev and A8 Alekseev8 All :nitely

axiomatizable normal extensions of

(

— are decidable8 Mathematical Logic Quarterly-

K

.

(535).ff—- 5'')8

"

"

Zakharyaschev and Popov- 5'?'

M8V8 Zakharyaschev and S8V8 Popov8 On the com2

plexity of Kripke countermodels in intuitionistic propositional calculus8 In Proceedings

of the 1nd Soviet5Finland Logic Col loquium- pages —ff.—0- 5'?'8 ]Russian78

"

"

Zakharyaschev- 5'fl—

M8V8 Zakharyaschev8 On intermediate logics8 Soviet Mathematics

Doklady- ff?3ff?(.ff??- 5'fl—8

"

"

Zakharyaschev- 5'fl(

M8V8 Zakharyaschev8 Normal modal logics containing

(8 Soviet

S

Mathematics Doklady- fffl3ff)ff.ff))- 5'fl(8

"

"

Zakharyaschev- 5'fl?

M8V8 Zakharyaschev8 On the disjunction property of superintu2

itionistic and modal logics8 Mathematical Notes- (ff3'[5.'[)- 5'fl?8

"

"

Zakharyaschev- 5'flfl

M8V8 Zakharyaschev8 Syntax and semantics of modal logics con2

taining

(8 Algebra and Logic- ff?3([fl.(fffl- 5'flfl8

S

5flff

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

"

"

Zakharyaschev- 5'fl'

M8V8 Zakharyaschev8 Syntax and semantics of intermediate log2

ics8 Algebra and Logic- fffl3ff0ff.ffflff- 5'fl'8

"

"

Zakharyaschev- 5''5

M8V8 Zakharyaschev8 Modal companions of superintuitionistic

logics3 syntax- semantics and preservation theorems8 Mathematics of the USSR:

Sbornik- 0fl3ff??.fffl'- 5''58

"

"

Zakharyaschev- 5''ff

M8V8 Zakharyaschev8 Canonical formulas for

(8 Part I3 Basic

K

results8 Journal of Symbolic Logic- )?35—??.5([ff- 5''ff8

"

"

Zakharyaschev- 5''(

M8V8 Zakharyaschev8 A new solution to a problem of Hosoi and

Ono8 Notre Dame Journal of Formal Logic- —)3()[.()?- 5''(8

"

"

K

Zakharyaschev- 5''0

M8V8 Zakharyaschev8 Canonical formulas for

(8 Part II3 Co:nal

subframe logics8 Journal of Symbolic Logic- 053(ff5.(('- 5''08

"

"

Zakharyaschev- 5''?a

M8V8 Zakharyaschev8 Canonical formulas for

(8 Part III3 the

K

:nite model property8 Journal of Symbolic Logic- 0ff- 5''?8 To appear8

"

"

Zakharyaschev- 5''?b

M8V8 Zakharyaschev8 Canonical formulas for modal and super2

intuitionistic logics3 a short outline8 In M8 de Rijke- editor- Advances in Intensional

Logic- pages 5'5.ff(—8 Kluwer Academic Publishers- 5''?8

Index

.,

-formula. 55

compactness. 21

!prime logic. 6

complete set of formulas. 6

-irreducible logic. 6

complex variety. 25

L

.

-complex logic. 25

complexity function. 161

L

.

-generated frame. 11. 61

configuration problem. 156

n-transitive logic. 6. 61

congruential logic. 166

actual world. 60

cover. 12

actual world condition. 61

cycle free frame. 18. 61

conservative formula. 86

amalgamability. 82

atom. 12. 16

d-cyclic set. 12

axiomatic basis. 6

deduction theorem. 7

axiomatization

deductively equivalent formulas. 7

finite. 8

degree of incompleteness. 38

independent. 8

depth of a frame. 13

problem. 17

descriptive frame. 11. 61

recursive. 8

difference operator. 168

Beth property. 69

disjunction property. 139

bimodal companion. 153

modal. 139

bisimulation. 168

distinguished point. 60

differentiated frame. 11. 61

canonical formula. 29

Dummett logic. 118

intuitionistic. 118

downward directness. 35

quasi-normal. 63

elementary logic. 36

canonicity. 19

essentially negative formula. 138

CDC. 28

closed domain. 28

finite embedding property. 56

closed domain condition. 28

finite model property

cluster assignment. 98

exponential. 161

cofinal subframe formula. 57

global. 23

cofinal subframe logic. 57

polynomial. 161

quasi-normal. 62

fixed point operator. 168

compact frame. 11

focus. 73

162

5fl(

M8 ZAKHARYASCHEV- F8 WOLTER- AND A8 CHAGROV

frame formula. 29

Noetherian frame. 27

fusion. 62

nominal. 168

G;odel translation. 112

non-iterative logic. 63

non-eliminability. 30

global derivability. 7

normal filter. 82

global Kripke completeness. 23

normal form. 53

graded modality. 168

Halldoen completeness. 88

open domain. 28. 117

Heyting algebra. 111

p-morphism. 11

inaccessible world. 60

independent set of formulas. 6

persistence. 19

polymodal frame. 61

polymodal logic. 60

inference rule

admissible. 159

derivable. 159

interpolant. 69

post-. 88

polynomially equivalent logics. 161

positive formula. 31

pretabularity. 68

prime filter. 113

prime formula. 6

interpolation property. 69

pseudo-Boolean algebra. 111

for a consequence relation. 80

intersection of logics. 6

quasi-normal logic. 79

intuitionistic frame. 113

intuitionistic modal frame. 126

reduced frame. 30

intuitionistic modal logic. 126

reduction. 11. 61

Jankov formula. 29

Kreisel!Putnam logic. 120

Kripke frame. 9

weak. 106

refined frame. 11

refined refined. 61

replacement function. 97

Rieger!Nishimura lattice. 113

L;ob axiom. 27

root. 9. 61

linear tense logic. 96

rooted frame. 9

local tabularity. 53

logic of a class of frames. 9

Sahlqvist formula. 36. 63

Scott logic. 120

Medvedev's logic. 125

semantical consequence. 160

minimal tense extension. 92

si-fragment. 119

Minsky machine. 156

si-logic. 111

modal companion. 119

simulation of a frame. 90

modal degree. 30

simulation of a logic. 90

modal matrix. 60

skeleton. 112

skeleton lemma. 115

negative formula. 31

Smetanich logic. 118

Nishimura formula. 112

splitting. 17

ADVANCED MODAL LOGIC

5fl)

union-. 17

splitting pair. 6

standard translation. 77

strict Kripke completeness. 17

strict sf-completeness. 56

strong global completeness. 23

strong Kripke completeness. 21

strongly positive formula. 33

structural completeness. 171

subframe. 27. 26. 67. 61. 117

cofinal. 56. 67

generated. 9. 61

subframe formula. 57

subframe logic. 57. 56

quasi-normal. 62

subreduction. 26

cofinal. 26

quasi-. 61

weak. 108

sum of logics. 6

superamalgamability. 82

superintuitionistic logic. 111

surrogate. 65

surrogate frame. 106

t-line logic. 103

tabularity. 67

Tarski's criterion. 8

tense frame. 92

tense logic. 92

tight frame. 11

time-line. 103

topological Boolean algebra. 112

undecidable formula. 159

uniform formula. 52

uniform interpolation. 88

universal frame of rank n. 13

universal modality. 68

untied formula. 37

upward closed set. 9

weak Kreisel!Putnam formula. 116


