1

Basic Concepts

Languages of propositional modal logic are propositional languages to which sen-
tential operators (usually called modalities or modal operators) have been added.
In spite of their syntactic simplicity, such languages turn out to be useful tools for
describing and reasoning about relational structures. A relational structure is a
non-empty set on which a number of relations have been deﬁned; they are wide-
spread in mathematics, computer science, artiﬁcial intelligence and linguistics, and
are also used to interpret ﬁrst-order languages.

Now, when working with relational structures we are often interested in struc-
tures possessing certain properties. Perhaps a certain transitive binary relation is
particularly important. Or perhaps we are interested in applications where ‘dead
ends,’ ‘loops,’ and ‘forkings’ are crucial, or where each relation is a partial func-
tion. Wherever our interests lie, modal languages can be useful, for modal oper-
ators are essentially a simple way of accessing the information contained in rela-
tional structures. As we will see, the local and internal access method that modali-
ties offer is strong enough to describe, constrain, and reason about many interesting
and important aspects of relational structures.

Much of this book is essentially an exploration and elaboration of these remarks.
The present chapter introduces the concepts and terminology we will need, and the
concluding section places them in historical context.

Chapter guide

Section 1.1: Relational Structures. Relational structures are deﬁned, and a num-

ber of examples are given.

Section 1.2: Modal Languages. We are going to talk about relational structures
using a number of different modal languages. This section deﬁnes the
basic modal language and some of its extensions.

Section 1.3: Models and Frames. Here we link modal languages and relational
structures. In fact, we introduce two levels at which modal languages can

1

2

1 Basic Concepts

the level of models (which we explore
be used to talk about structures:
in Chapter 2) and the level of frames (which is examined in Chapter 3).
This section contains the fundamental satisfaction deﬁnition, and deﬁnes
the key logical notion of validity.

Section 1.4: General Frames. In this section we link modal languages and rela-
tional structures in yet another way: via general frames. Roughly speak-
ing, general frames provide a third level at which modal languages can be
used to talk about relational structures, a level intermediate between those
provided by models and frames. We will make heavy use of general frames
in Chapter 5.

Section 1.5: Modal Consequence Relations. Which conclusions do we wish to
draw from a given a set of modal premises? That is, which consequence
relations are appropriate for modal languages? We opt for a local conse-
quence relation, though we note that there is a global alternative.
Section 1.6: Normal Modal Logics. Both validity and local consequence are de-
ﬁned semantically (that is, in terms of relational structures). However, we
want to be able to generate validities and draw conclusions syntactically.
We take our ﬁrst steps in modal proof theory and introduce Hilbert-style
axiom systems for modal reasoning. This motivates a concept of central
importance in Chapters 4 and 5: normal modal logics.

Section 1.7: Historical Overview. The ideas introduced in this chapter have a long
and interesting history. Some knowledge of this will make it easier to
understand developments in subsequent chapters, so we conclude with a
historical overview that highlights a number of key themes.

1.1 Relational Structures
Deﬁnition 1.1 A relational structure is a tuple � whose ﬁrst component is a non-
empty set � called the universe (or domain) of �, and whose remaining compo-
nents are relations on � . We assume that every relational structure contains at
least one relation. The elements of � have a variety of names in this book, includ-
ing: points, states, nodes, worlds, times, instants and situations. �

An attractive feature of relational structures is that we can often display them as
simple pictures, as the following examples show.

Example 1.2 Strict partial orders (SPOs) are an important type of relational struc-
ture. A strict partial order is a pair ��� �� such that � is irreﬂexive (�� ����) and
transitive (���� �������� � ��� �). A strict partial order � is a linear order (or
a total order) if it also satisﬁes the trichotomy condition: ��� ������ � ������.
An example of an SPO is given in Figure 1.1, where � � ��, �, �, �, �, �, ��, ���

1.1 Relational Structures

3

��

�

�

�

�

�

��

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

Fig. 1.1. A strict partial order.

and ��� means ‘� and � are different, and � can be divided by �.’ Obviously this is
not a linear order. On the other hand, if we deﬁne ��� by ‘� is numerically smaller
than �,’ we obtain a linear order over the same universe � . Important examples of
� ��, the natural numbers, integers,
� �� and �
linear orders are �
rationals and reals in their usual order. We sometimes use the notation �� � �� for

� ��, �

� ��, �

�

�

�

�

�

�

� ��.
In many applications we want to work not with strict partial orders, but with
plain old partial orders (POs). We can think of a partial order as the reﬂexive
closure of a strict partial order; that is, if � is a strict partial order on � , then
� � ���� �� � � � � � is a partial order (for more on reﬂexive closures, see Exer-
cise 1.1.3). Thus partial orders are transitive, reﬂexive (�� ���) and antisymmetric
(��� ���� � ��� � � � ��). If a partial order is connected (��� ���� � ����)
it is called a reﬂexive linear order (or a reﬂexive total order).

If we interpret the relation in Figure 1.1 reﬂexively (that is, if we take ��� to
mean ‘� and � are equal, or � can be divided by �’) we have a simple example of
a partial order. Obviously, it is not a reﬂexive linear order. Important examples of
� ��, the
reﬂexive linear orders include �
natural numbers, integers, rationals and reals under their respective ‘less-than-or-
equal-to’ orderings. �

� �� (or �� � ��), �

� �� and �

� ��, �

�

�

�

�

�

Example 1.3 Labeled Transition Systems (LTSs), or more simply, transition sys-
tems, are a simple kind of relational structure widely used in computer science. An
� � � ��) where � is a non-empty set of states, � is a non-
LTS is a pair ��� ��
empty set (of labels), and for each � � �, �
� � � � . Transition systems can
be viewed as an abstract model of computation: the states are the possible states
means that there is
of a computer, the labels stand for programs, and ��� �� � �
an execution of the program � that starts in state � and terminates in state �. It is
natural to depict states as nodes and transitions �
In Figure 1.2 a transition system with states �

as directed arrows.

� �

� �

� �

�

�

�

�

�

�

�

shown. Formally, �

� ���

� �

�� ��

� �

��, while �

���

� �

�

�

��. This transition system is actually rather special, for it is deterministic:

�

�

�

�

�

�

�

�

�

� ���

and labels �� �� � is
�� and �

� �

�

4

1 Basic Concepts

�

�

��

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

Fig. 1.2. A deterministic transition system.

��

if we are in a state where it is possible to make one of the three possible kinds of
transition (for example, an � transition) then it is ﬁxed which state that transition
, �
will take us to. In short, the relations �
Deterministic transition systems are important, but in theoretical computer sci-
ence it is more usual to take non-deterministic transition systems as the basic model
of computation. A non-deterministic transition system is one in which the state we
reach by making a particular kind of transition from a given state need not be ﬁxed.
That is, the transition relations do not have to be partial functions, but can be arbi-
trary relations.

are all partial functions.

and �

�

�

�

�

�

��

�

�

�

�

�

�

�

�

�

�

�

� �

�

�

�

�

�

�

�

�

�

�

Fig. 1.3. A non-deterministic transition system.

��

In Figure 1.3 a non-deterministic transition system is shown: � is now a non-
there are two possibilities:
deterministic program, for if we execute it in state �
either we loop back into �

, or we move to �

.

�

�

�

Transition systems play an important role in this book. This is not so much be-
cause of their computational interpretation (though that is interesting) but because
of their sheer ubiquity. Sets equipped with collections of binary relations are one
of the simplest types of mathematical structures imaginable, and they crop up just
about everywhere. �

Example 1.4 For our next example we turn to the branch of artiﬁcial intelligence
called knowledge representation. A central concern of knowledge representation
is objects, their properties, their relations to other objects, and the conclusions one
can draw about them. For example, Figure 1.4 represents some of the ways Mike
relates to his surroundings.

One conclusion that can be drawn from this representation is that Sue has chil-

1.1 Relational Structures

5

Sue

�

�

son-of

�

�

�

BMW

owns

�

Mike

loves

�

�

Diana

�

�

�

�

�

�

�

�

Fig. 1.4. Mike and others.

�

�

�

�

dren. Others are not so clear. For example, does Mike love Sue, and does he
love his BMW? Assuming that absence of a not loves arc (like that connecting
the Mike and the Diana nodes) means that the loves relation holds, this is a safe
conclusion to draw. There are often such ‘gaps’ between pictures and relational
structures, and to ﬁll them correctly (that is, to know which relational structure
the picture corresponds to) we have to know which diagrammatic conventions are
being assumed.

Let’s take the picture at face value. It gives us a set �

Diana
together with binary relations son-of, owns, and not loves. So we have here
another labeled transition system. �

Mike

Sue

BMW

�

�

�

�

Example 1.5 Finite trees are ubiquitous in linguistics. For example, the tree de-
picted in Figure 1.5 represents some simple facts about phrase-structure, namely
that a sentence (S) can consist of a noun phrase (NP) and a verb phrase (VP); an NP
can consist of a proper noun (PN); and VPs can consist of a transitive verb (TV)
and an NP.

S

�

�

NP

�

�

�

VP

�

�

�

�

�

�

PN

TV

�

�

�

NP

PN

Fig. 1.5. A ﬁnite decorated tree.

�

Trees play an important role in this book, so we will take this opportunity to deﬁne
them. We ﬁrst introduce the following important concepts.

Deﬁnition 1.6 Let � be a non-empty set and � a binary relation on � . Then �
�,
the transitive closure of �, is the smallest transitive relation on � that contains �.
That is,

�

�

�

�

��

� �

� is a transitive binary relation on � � � � �

�

��

Furthermore, �

�, the reﬂexive transitive closure of �, is the smallest reﬂexive and

�

6

1 Basic Concepts

transitive relation on � containing �. That is,

�

�

�

�

��

� �

� is a reﬂexive transitive binary relation on � � � � �

�

�� �

�

�

� � (� � �) from � such that for each � � � we have ��

�� holds if and only if there is a sequence of elements � � �

,
, �
. That
�� means that � is reachable from � in a ﬁnite number of �-steps. Thus

Note that �
. . . , �
is, �
transitive closure is a natural and useful notion; see Exercise 1.1.3.

��

�

�

�

�

�

�

�

With these concepts at our disposal, it is easy to say what a tree is.

Deﬁnition 1.7 A tree � is a relational structure �� � � � where:

(i) � , the set of nodes, contains a unique � � � (called the root) such that

�� � � �

�

��.

(ii) Every element of � distinct from � has a unique �-predecessor; that is, for

every � �� � there is a unique �

�

� � such that � �

�

�.

(iii) � is acyclic; that is, ����

�

��. (It follows that � is irreﬂexive.) �

Clearly, Figure 1.5 contains enough information to give us a tree �� � � � in the sense
just deﬁned: the nodes in � are the displayed points, and the relation � is indicated
by means of a straight line segment drawn from a node to a node immediately
below (that is, � is the obvious successor or daughter-of relation). The root of the
tree is the topmost node (the one labeled S).

But the diagram also illustrates something else: often we need to work with
structures consisting of not only a tree �� � � �, but a whole lot else besides. For
example, linguists wouldn’t be particularly interested in the bare tree �� � � � just
deﬁned, rather they’d be interested in (at least) the structure

LEFT-OF

� S� NP� VP� PN� TV��

�� � ��

Here S, NP, VP, PN, and TV are unary relations on � (note that S and � are distinct
symbols). These relations record the information attached to each node, namely the
fact that some nodes are noun phrase nodes, while others are proper name nodes,
sentential nodes, and so on. LEFT-OF is a binary relation which captures the left-
to-right aspect of the above picture; the fact that the NP node is to the left of the
VP node might be linguistically crucial.

Similar things happen in mathematical contexts. Sometimes we will need to
work with relational structures which are much richer than the simple trees �� � � �
just deﬁned, but which, perhaps in an implicit form, contain a relation with all the
properties required of �. It is useful to have a general term for such structures; we
will call them tree-like. A formal deﬁnition here would do more harm than good,
but in the text we will indicate, whenever we call a structure tree-like, where this
implicit tree �� � � � can be found. That is, we will say, unless it is obvious, which
deﬁnable relation in the structure satisﬁes the conditions of Deﬁnition 1.7. One of

1.1 Relational Structures

7

the most important examples of tree-like structures is the Rabin structure, which
we will meet in Section 6.3.

One often encounters the notion of a tree deﬁned in terms of the (reﬂexive) tran-
sitive closure of the successor relation. Such trees we call (reﬂexive and) transitive
trees, and they are dealt with in Exercises 1.1.4 and 1.1.5 �

Example 1.8 We have already seen that labeled transition systems can be regarded
as a simple model of computation. Indeed, they can be thought of as models for
practically any dynamic notion: each transition takes us from an input state to an
output state. But this treatment of states and transitions is rather unbalanced: it
is clear that transitions are second-class citizens. For example, if we talked about
LTSs using a ﬁrst-order language, we couldn’t name transitions using constants
(they would be talked about using relation symbols) but we could have constants
for states. But there is a way to treat transitions as ﬁrst-class citizens: we can work
with arrow structures.

The objects of an arrow structure are things that can be pictured as arrows. As
concrete examples, the mathematically inclined reader might think of vectors, or
functions or morphisms in some category; the computer scientist of programs; the
linguist of the context changing potential of a grammatically well-formed piece of
text or discourse; the philosopher of some agent’s cognitive actions; and so on. But
note well: although arrows are the prime citizens of arrow structures, this does not
mean that they should always be thought of as primitive entities. For example, in
a two-dimensional arrow structure, an arrow � is thought of as a pair ��
� of
which �

represents the starting point of �, and �

its endpoint.

� �

�

�

�

�

Having ‘deﬁned’ the elements of arrow structures to be objects graphically rep-
resentable as arrows, we should now ask: what are the basic relations which hold
between arrows? The most obvious candidate is composition: vector spaces have
an additive structure, functions can be composed, language fragments can be con-
catenated, and so on. So the central relation on arrows will be a ternary composi-
tion relation �, where � ��� says that arrow � is the outcome of composing arrow
� with arrow � (or conversely, that � can be decomposed into � and �). Note that
in many concrete examples, � is actually a (partial) function; for example, in the
two-dimensional framework we have

� ��� iff �

� �

� �

� �

and �

� �

�

�

�

�

�

�

�

(1.1)

What next? Well, in all the examples listed, the composition function has a neutral
element; think of the identity function or the SKIP-program. So, arrow structures
will contain degenerate arrows, transitions that do not lead to a different state.
Formally, this means that arrow structures will contain a designated subset � of
identity arrows; in the pair-representation, � will be (a subset of) the diagonal:

� � iff �

� �

�

�

�

(1.2)

8

1 Basic Concepts

Another natural relation is converse. In linguistics and cognitive science we might
view this as an ‘undo’ action (perhaps we’ve made a mistake and need to recover)
and in many ﬁelds of mathematics arrow-like objects have converses (vectors) or
inverses (bijective functions). So we’ll also give arrow structures a binary reverse
relation �. Again, in many cases this relation will be a partial function. For exam-
ple, in the two-dimensional picture, � is given by

��� iff �

and �

� �

� �

�

�

�

�

�

(1.3)

Although there are further natural candidates for arrow relations (notably some
notion of iteration) we’ll leave it at this. And now for the formal deﬁnition: an
arrow frame is a quadruple �
� ��� �� �� � � such that �, � and � are a ternary,
a binary and a unary relation on � , respectively. Pictorially, we can think of them
as follows:

��

�

�

�

�

�

�

��

�

�

�

�

�

�

�

�

�

�

��
�

�

�

�

� ���

� �

���

�

The two-dimensional arrow structure, in which the universe consists of all pairs
over the set � (and the relations �, � and � are given by (1.1), (1.3) and (1.2),
respectively) is called the square over � , notation: �
. The square arrow frame
over � can be pictorially represented as a full graph over � : each arrow object
; the relations
are as pictured above. Alternatively, square arrow frames can be represented two-
dimensionally, cf. the pictures in Example 1.27. �

can be represented as a ‘real’ arrow from �

� in �

to �

� �

��

�

�

�

�

�

�

Exercises for Section 1.1
1.1.1 Let �
the binary relation � on � by putting �

�� �

� be a quasi-order; that is, assume that � is transitive and reﬂexive. Deﬁne
� iff ��� and ���.

�

(a) Show that � is an equivalence relation

� denote the equivalence class of � under this relation, and deﬁne the following rela-

Let �
tion on the collection of equivalence classes: �

�

� iff ���.

�

�

� � �

(b) Show that this is well-deﬁned.
(c) Show that � is a partial order.

1.1.2 Let � be a transitive relation on a ﬁnite set � . Prove that � is well-founded iff � is
irreﬂexive. (� is called well-founded if there are no inﬁnite paths � � � ��

.)

��

��

�

�

�

1.1.3 Let � be a binary relation on � . In Example 1.2 we deﬁned the reﬂexive closure
�. But we can also give a deﬁnition analogous to those
of � to be �

� ��

�� �

� �

�

�

�

1.2 Modal Languages

9

� and �

of �
contains �:

� in Deﬁnition 1.6, namely that it is the smallest reﬂexive relation on � that

r

�

�

�

�

�

�

�

�

� is a reﬂexive binary relation on �

�

�

�

�

�

�

�

Explain why this new deﬁnition (and the deﬁnitions of �
the equivalence of the two deﬁnitions of reﬂexive closure. Finally, show that �
only if there is a sequence of elements �
� � � we have ��
transitive closure.

�) are well deﬁned. Show
�� if and
� from � such that for each
, and give an analogous sequence-based deﬁnition of reﬂexive

� and �

, . . . , �

, �

��

�

�

�

�

�

�

�

�

�

�

1.1.4 A transitive tree is an SPO
for all �
and linearly ordered by �.

� and (ii) for each �

�

� such that (i) there is a root �

�

� � �

� , the set �

�

�

�

�

�

� � �

� satisfying � � �
� of predecessors of � is ﬁnite

�

(a) Prove that if �
(b) Prove that �

� is a tree then �

� � �

�

� is a transitive tree.

� � �

� is a transitive tree iff �

� is a tree, where �

is the immediate

�

�

� � �

� � �

successor relation given by ��

� iff � � � and � � � � � for no �

�

� .

�

(c) Under which conditions does the converse of (a) hold?

1.1.5 Deﬁne the notion of a reﬂexive and transitive tree, such that if �

� � �

� is a tree then

�

� is a reﬂexive and transitive tree.

�

� � �

1.1.6 Show that the following formulas hold on square arrow frames:

��

���

���

�

�

�,

��

�

� �

�

� ���

� �

�

�

�,

���

(a) �
(b) �
(c) �

��

�

�

�

� ��

�

� ��

�

�

� ���

� ��

�

��

�

�

� � �

�

�

�

�

�

�

�

�

�

�

�

��.

1.2 Modal Languages
It’s now time to meet the modal languages we will be working with. First, we
introduce the basic modal language. We then deﬁne modal languages of arbitrary
similarity type. Finally we examine the following extensions of the basic modal
language in more detail: the basic temporal language, the language of proposi-
tional dynamic logic, and a language of arrow logic.

Deﬁnition 1.9 The basic modal language is deﬁned using a set of proposition let-
ters (or proposition symbols or propositional variables) � whose elements are usu-
ally denoted �, �, �, and so on, and a unary modal operator � (‘diamond’). The
well-formed formulas � of the basic modal language are given by the rule

� ��� � � � � �� � � � � �

��

�

where � ranges over elements of �. This deﬁnition means that a formula is either a
proposition letter, the propositional constant falsum (‘bottom’), a negated formula,
a disjunction of formulas, or a formula preﬁxed by a diamond.

Just as the familiar ﬁrst-order existential and universal quantiﬁers are duals to
each other (in the sense that �� � � ��� ��), we have a dual operator � (‘box’)

10

1 Basic Concepts

��. We also make use of the classi-
for our diamond which is deﬁned by �
cal abbreviations for conjunction, implication, bi-implication and the constant true
(‘top’): � � � �� ���� � ���, � � � �� �� � �, � � � �� �� � �� � �� � ��
and � �� � �. �

� �� �

�

�

�

� �

Although we generally assume that the set � of proposition letters is a countably
� � � ��, occasionally we need to make other assumptions. For in-
inﬁnite ��
stance, when we are after decidability results, it may be useful to stipulate that � is
ﬁnite, while doing model theory or frame theory we may need uncountably inﬁnite
languages. This is why we take � as an explicit parameter when deﬁning the set of
modal formulas.

�

�

� �

� (‘whatever is necessary is possible’) and all instances of � �

Example 1.10 Three readings of diamond and box have been extremely inﬂuen-
� can be read as ‘it is possibly the case that �.’ Under this reading,
tial. First, �
� means ‘it is not possible that not �,’ that is, ‘necessarily �,’ and examples
of formulas we would probably regard as correct principles include all instances
of �
(‘whatever is, is possible’). The status of other formulas is harder to decide. Should
� (‘whatever is, is necessarily possible’) be regarded as a general truth
� (‘whatever is possible, is
about necessity and possibility? Should �
necessarily possible’)? Are any of these formulas linked by a modal notion of log-
ical consequence, or are they independent claims about necessity and possibility?
These are difﬁcult (and historically important) questions. The relational semantics
deﬁned in the following section offers a simple and intuitively compelling frame-
work in which to discuss them.

� �

� �

��

��

�

�

Second, in epistemic logic the basic modal language is used to reason about
� for ‘the agent knows that �’ it is usual to
knowledge, though instead of writing �
write � �. Given that we are talking about knowledge (as opposed to, say, belief
or rumor), it seems natural to view all instances of � � � � as true: if the agent
really knows that �, then � must hold. On the other hand (assuming that the agent
is not omniscient) we would regard � � � � as false. But the legitimacy of other
principles is harder to judge (if an agent knows that �, does she know that she
knows it?). Again, a precise semantics brings clarity.

Third, in provability logic �

� is read as ‘it is provable (in some arithmetical
theory) that �.’ A central theme in provability logic is the search for a complete
axiomatization of the provability principles that are valid for various arithmetical
theories (such as Peano Arithmetic). The L¨ob formula �
� plays a
key role here. The arithmetical ramiﬁcations of this formula lie outside the scope
of the book, but in Chapters 3 and 4 we will explore its modal content. �

� � �� �

�

�

�

That’s the basic modal language. Let’s now generalize it. There are two obvious
ways to do so. First, there seems no good reason to restrict ourselves to languages

1.2 Modal Languages

11

with only one diamond. Second, there seems no good reason to restrict ourselves
to modalities that take only a single formula as argument. Thus the general modal
languages we will now deﬁne may contain many modalities, of arbitrary arities.

Deﬁnition 1.11 A modal similarity type is a pair � � �� � �� where � is a non-
�. The elements of � are called modal
empty set, and � is a function � �
operators; we use � (‘triangle’), �
, . . . to denote elements of �. The function
, �
� � a ﬁnite arity, indicating the number of arguments
� assigns to each operator �
� can be applied to.

�

�

In line with Deﬁnition 1.9, we often refer to unary triangles as diamonds, and
or ���, where � is taken from some index set. We often assume
denote them by �
that the arity of operators is known, and do not distinguish between � and �. �

�

Deﬁnition 1.12 A modal language ��
type � � �� � �� and a set of proposition letters �. The set ����
formulas over � and � is given by the rule

�� � �� is built up using a modal similarity
�� � �� of modal

� �� � � � � �� � �

� �

�

��

� � � � � �

��

�

�

�

�

�

�

�

�

where � ranges over elements of �. �

�

.

� instead of �

The similarity type of the basic modal language is called �
In the sequel we
sometimes state results for modal languages of arbitrary similarity types, give the
proof for similarity types with diamonds only, and leave the general case as an ex-
ercise. For binary modal operators, we often use inﬁx notation; that is, we usually
��� ��. One other thing: note that our deﬁnition permits
write �
nullary modalities (or modal constants), triangles that take no arguments at all.
Such modalities can be useful — we will see a natural example when we discuss
arrow logic — but they play a relatively minor role in this book. Syntactically (and
indeed, semantically) they are rather like propositional variables; in fact, they are
best thought of as propositional constants.

�

�

� � the dual � of � is deﬁned as �

Deﬁnition 1.13 We now deﬁne dual operators for non-nullary triangles. For each
�. The
dual of a triangle of arity at least � is called a nabla. As in the basic modal language,
the dual of a diamond is called a box, and is written �

or ���. �

� � � � � ��

� � � � � �

� �� �

���

��

�

�

�

�

�

Three extensions of the basic modal language deserve special attention. Two of
these, the basic temporal language and the language of propositional dynamic logic
will be frequently used in subsequent chapters. The third is a simple language of
arrow logic; it will provide us with a natural example of a binary modality.

�

Example 1.14 (The Basic Temporal Language) The basic temporal language is
built using a set of unary operators � � ��� �� �� ��. The intended interpretation

12

1 Basic Concepts

of a formula �� �� is ‘� will be true at some Future time,’ and the intended inter-
pretation of �� �� is ‘� was true at some Past time.’ This language is called the
basic temporal language, and it is the core language underlying a branch of modal
logic called temporal logic. It is traditional to write �� � as � and �� � as � , and
their duals are written as � and �, respectively. (The mnemonics here are: ‘it is
always Going to be the case’ and ‘it always Has been the case.’)

We can express many interesting assertions about time with this language. For
example, � � � �� �, says ‘whatever has happened will always have happened,’
and this seems a plausible candidate for a general truth about time. On the other
hand, if we insist that � � � � � � must always be true, it shows that we are
thinking of time as dense: between any two instants there is always a third. And if
we insist that �� � � � �� (the McKinsey formula) is true, for all propositional
symbols �, we are insisting that atomic information true somewhere in the future
eventually settles down to being always true. (We might think of this as reﬂecting
a ‘thermodynamic’ view of information distribution.)

One ﬁnal remark: computer scientists will have noticed that the binary until
modality is conspicuous by its absence. As we will see in the following chapter,
the basic temporal language is not strong enough to express until. We examine a
language containing the until operator in Section 7.2. �

Example 1.15 (Propositional Dynamic Logic) Another important branch of mo-
dal logic, again involving only unary modalities, is propositional dynamic logic.
PDL, the language of propositional dynamic logic, has an inﬁnite collection of
diamonds. Each of these diamonds has the form ���, where � denotes a (non-
deterministic) program. The intended interpretation of ���� is ‘some terminating
execution of � from the present state leads to a state bearing the information �.’
The dual assertion �� �� states that ‘every execution of � from the present state leads
to a state bearing the information �.’

So far, there’s nothing really new — but a simple idea is going to ensure that
PDL is highly expressive: we will make the inductive structure of the programs
explicit in PDL’s syntax. Complex programs are built out of basic programs using
some repertoire of program constructors. By using diamonds which reﬂect this
structure, we obtain a powerful and ﬂexible language.

Let us examine the core language of PDL. Suppose we have ﬁxed some set of
basic programs �, �, �, and so on (thus we have basic modalities ���, ���, ���, . . .
at our disposal). Then we are allowed to deﬁne complex programs � (and hence,
modal operators ���) over this base as follows:

(choice) if �

and �
The program �

�

�

are programs, then so is �

.

� �

(non-deterministically) executes �

or �

.

� �

�

�

�

�

�

�

1.2 Modal Languages

13

(composition) if �

and �
This program ﬁrst executes �

are programs, then so is �
.

�

�

�

�

.

� �

�

�

(iteration) if � is a program, then so is �

and then �
�.

� is a program that executes � a ﬁnite (possibly zero) number of times.

�

�

�

�

�

�

�

� �

� �

�, ��

� and ��

� and ��

� are modal operators,
For the collection of diamonds this means that if ��
�. This notation makes it straightforward to
then so are ��
describe properties of program execution. Here is a fairly straightforward example.
�� says that a state bearing the information � can
The formula ��
be reached by executing � a ﬁnite number of times if and only if either we already
have the information � in the current state, or we can execute � once and then ﬁnd
a state bearing the information � after ﬁnitely many more iterations of �. Here’s a
far more demanding example:

�� � � � �� � �

�

�

�

�

�

�

��

��� � �� ��� � �� � ��

����

This is Segerberg’s axiom (or the induction axiom) and the reader should try work-
ing out what exactly it is that this formula says. We discuss this formula further in
Chapter 3, cf. Example 3.10.

If we conﬁne ourselves to these three constructors (and in this book for the most
part we do) we are working with a version of PDL called regular PDL. (This is
because the three constructors are the ones used in Kleene’s well-known analysis of
regular programs.) However, a wide range of other constructors have been studied.
Here are two:

(intersection) if �

�

�

are programs, then so is �

and �
The intended meaning of �
if � is a formula, then �� is a program.
This program tests whether � holds, and if so, continues; if not, it fails.

is: execute both �

, in parallel.

and �

.

� �

� �

�

�

�

�

�

�

(test)

and �

�� is that if we execute
To ﬂesh this out a little, the intended reading of ��
in the present state, then there is at least one state reachable by both
both �
programs which bears the information �. This is a natural constructor for a variety
of purposes, and we will make use of it in Section 6.5.

� �

�

�

�

�

The key point to note about the test constructor is its unusual syntax: it allows us
to make a modality out of a formula. Intuitively, this modality accesses the current
state if the current state satisﬁes �. On its own such a constructor is uninteresting
(����� simply means � � �). However, when other constructors are present, it can
be used to build interesting programs. For example, ��� � �� � ���� � �� is ‘if
then

else

�

�.’

�

Nothing prevents us from viewing the basic programs as deterministic, and we

will discuss a fragment of deterministic PDL (DPDL) in Section 6.5 �

14

1 Basic Concepts

Example 1.16 (An Arrow Language) A similarity type with modal operators
of arrow logic. The language of arrow logic
other than diamonds, is the type �
is designed to talk about the objects in arrow structures (entities which can be
pictured as arrows). The well-formed formulas � of the arrow language are given
by the rule

�

� �� � � � � �� � � � � � � � � � �� � �’�

That is, �’ (‘identity’) is a nullary modality (a modal constant), the ‘converse’ oper-
ator � is a diamond, and the ‘composition’ operator � is a dyadic operator. Possible
readings of these operators are:

�’

��

identity
converse

‘skip’
‘� conversely’

� � � composition ‘ﬁrst �, then �’� �

Example 1.17 (Feature Logic and Description Logic) As we mentioned in the
Preface, researchers developing formalisms for describing graphs have sometimes
(without intending to) come up with notational variants of modal logic. For ex-
ample, computational linguists use Attribute-Value Matrices (AVMs) for describ-
ing feature structures (directed acyclic graphs that encode linguistic information).
Here’s a fairly typical AVM:

AGREEMENT

PERSON
NUMBER plural

1st

�

�

�

�

CASE

dative

But this is just a two dimensional notation for the following modal formula

�

�

AGREEMENT
�dative

CASE

�

�

PERSON

�1st � �

NUMBER

�plural� �

���

Similarly, researchers in AI needing a notation for describing and reasoning about
ontologies developed description logic. For example, the concept of ‘being a hired
killer for the mob’ is true of any individual who is a killer and is employed by a
gangster. In description logic we can deﬁne this concept as follows:

killer

employer

gangster

� �

�

But this is simply the following modal formula lightly disguised:

killer

employer

gangster

� �

�

It turns out that the links between modal logic on the one hand, and feature and
description logic on the other, are far more interesting than these rather simple ex-
amples might suggest. A modal perspective on feature or description logic capable

1.2 Modal Languages

15

of accounting for other important aspects of these systems (such as the ability to
talk about re-entrancy in feature structures, or to perform ABox reasoning in de-
scription logic) must make use of the kinds of extended modal logics discussed in
Chapter 7 (in particular, logics containing the global modality, and hybrid logics).
Furthermore, some versions of feature and description logic make use of ideas
from PDL, and description logic makes heavy use of counting modalities (which
say such things as ‘at most 3 transitions lead to a � state’). �

Substitution

Throughout this book we’ll be working with the syntactic notion of one formula
In order to deﬁne this notion we ﬁrst
being a substitution instance of another.
introduce the concept of a substitution as a function mapping proposition letters to
variables.

Deﬁnition 1.18 Suppose we’re working a modal similarity type � and a set � of
proposition letters. A substitution is a map � � � �
Now such a substitution � induces a map ���

�� � ��.

�� � �� �

�� � ��

����

����

����

�

�

which we can recursively deﬁne as follows:

�

�

� �

�

�

� ����

�

�

����

� ��

�

�

�

�� � ��

� �

� �

�

�

�

��

� � � � � �

��

�

��

� � � � � �

��

�

�

�

�

�

�

�

This deﬁnition spells out exactly what is meant by carrying out uniform substitu-
tion. Finally, we say that � is a substitution instance of � if there is some substitu-
tion � such that �

� �. �

�

To give an example, if � is the substitution that maps � to � �
and leaves all other proposition letters untouched, then we have

�, � to ��

�

� � �

�� � � � ��

� ��� �

�� � �

� � �� � ���

�

�

��

Exercises for Section 1.2
1.2.1 Using � � to mean ‘the agent knows that �’ and � � to mean ‘it is consistent with
what the agent knows that �,’ represent the following statements.

(a) If � is true, then it is consistent with what the agent knows that she knows that �.
(b) If it is consistent with what the agent knows that �, and it is consistent with what
the agent knows that �, then it is consistent with what the agent knows that �
�.
(c) If the agent knows that �, then it is consistent with what the agent knows that �.

�

16

1 Basic Concepts

(d) If it is consistent with what the agent knows that it is consistent with what the agent

knows that �, then it is consistent with what the agent knows that �.

Which of these seem plausible principles concerning knowledge and consistency?

1.2.2 Suppose �
� be understood?
� is interpreted as ‘� is permissible’; how should �
List formulas which seem plausible under this interpretation. Should the L¨ob formula

�

�

�

�

�

� �

�

�

� be on your list? Why?

1.2.3 Explain how the program constructs ‘while � do �’ and ‘repeat � until �’
can be expressed in PDL.

1.2.4 Consider the following arrow formulas. Do you think they should be always true?

�’ �

�

��

�

��

�

� � �

� �

�

�

�

��

�

�

�

�

�

��

� �

�

� � �

�

� �

1.2.5 Show that ‘being-a-substitution-instance-of’ is a transitive concept. That is, show
that if � is a substitution instance of �, and � is a substitution instance of �, then � is a
substitution instance of �.

1.3 Models and Frames

Although our discussion has contained many semantically suggestive phrases such
as ‘true’ and ‘intended interpretation’, as yet we have given them no mathemat-
ical content. The purpose of this (key) section is to put that right. We do so by
interpreting our modal languages in relational structures. In fact, by the end of the
section we will have done this in two distinct ways: at the level of models and at
the level of frames. Both levels are important, though in different ways. The level
of models is important because this is where the fundamental notion of satisfaction
(or truth) is deﬁned. The level of frames is important because it supports the key
logical notion of validity.

Models and satisfaction

We start by deﬁning frames, models, and the satisfaction relation for the basic
modal language.

Deﬁnition 1.19 A frame for the basic modal language is a pair �
that

� ��� �� such

(i) � is a non-empty set.
(ii) � is a binary relation on � .

1.3 Models and Frames

17

That is, a frame for the basic modal language is simply a relational structure bearing
a single binary relation. We remind the reader that we refer to the elements of �
by many different names (see Deﬁnition 1.1).

A model for the basic modal language is a pair �

� � �, where � is a frame
for the basic modal language, and � is a function assigning to each proposition
letter � in � a subset � ��� of � . Informally we think of � ��� as the set of points
in our model where � is true. The function � is called a valuation. Given a model
� � �, we say that � is based on the frame �, or that � is the frame

� �

� �

�

�

�

underlying �. �

Note that models for the basic modal language can be viewed as relational struc-
tures in a natural way, namely as structures of the form:

��� �� � ���� � ���� � ���� � � ���

That is, a model is a relational structure consisting of a domain, a single binary
relation �, and the unary relations given to us by � . Thus, viewed from a purely
structural perspective, a frame � and a model � based on �, are simply two re-
lational models based on the same universe; indeed, a model is simply a frame
enriched by a collection of unary relations.

But in spite of their mathematical kinship, frames and models are used very dif-
ferently. Frames are essentially mathematical pictures of ontologies that we ﬁnd
interesting. For example, we may view time as a collection of points ordered by
a strict partial order, or feel that a correct analysis of knowledge requires that we
postulate the existence of situations linked by a relation of ‘being an epistemic
alternative to.’ In short, we use the level of frames to make our fundamental as-
sumptions mathematically precise.

The unary relations provided by valuations, on the other hand, are there to dress
our frames with contingent information. Is it raining on Tuesday or not? Is the
? Is a situation where Janet does not love him an
system write-enabled at time �
epistemic alternative for John? Such information is important, and we certainly
need to be able to work with it — nonetheless, statements only deserve the de-
scription ‘logical’ if they are invariant under changes of contingent information.
Because we have drawn a distinction between the fundamental information given
by frames, and the additional descriptive content provided by models, it will be
straightforward to deﬁne a modally reasonable notion of validity.

�

But this is jumping ahead. First we must learn how to interpret the basic modal
language in models. This we do by means of the following satisfaction deﬁnition.

� ��� �� � �. Then we induc-
Deﬁnition 1.20 Suppose � is a state in a model �
tively deﬁne the notion of a formula � being satisﬁed (or true) in � at state � as

18

follows:

1 Basic Concepts

�

� �

�

� iff � � � ���� where � � �

�

� �

�

�

never

�

� �

�

�� iff not �

� �

�

�

�

� �

�

� � � iff �

� �

� or �

�

� �

�

�

�

� �

�

�

� iff

for some � � � with ��� we have �

�

� �

��

(1.4)

It follows from this deﬁnition that �
that ���, we have �
state � of a model �, notation: �

� if and only if for all � � � such
�. Finally, we say that a set � of formulas is true at a
�, if all members of � are true at �. �

� �

� �

� �

�

�

�

�

Note that this notion of satisfaction is intrinsically internal and local. We evaluate
formulas inside models, at some particular state � (the current state). Moreover,
� works locally: the ﬁnal clause (1.4) treats �
� as an instruction to scan states
in search of one where � is satisﬁed. Crucially, only states �-accessible from the
current one can be scanned by our operators. Much of the characteristic ﬂavor of
modal logic springs from the perspective on relational structures embodied in the
satisfaction deﬁnition.

If � does not satisfy � at � we often write �

refuted at �. When � is clear from the context, we write �

�, and say that � is false or
� and
�. It is convenient to extend the valuation � from proposition
letters to arbitrary formulas so that � ��� always denotes the set of states at which
� is true:

� for �

� for �

� � �

� � �

� �

� �

�

�

�

�

�

� ��� �� �� �

� �

���

�

�

�

�) if it is satisﬁed at all points in � (that is, if �

Deﬁnition 1.21 A formula � is globally or universally true in a model � (nota-
�, for all
tion: �
� � � ). A formula � is satisﬁable in a model � if there is some state in � at
which � is true; a formula is falsiﬁable or refutable in a model if its negation is
satisﬁable.

� �

�

A set � of formulas is globally true (satisﬁable, respectively) in a model � if

�

� �

�

� for all states � in � (some state � in �, respectively). �

Example 1.22 (i) Consider the frame �

� ���

, �

, �

, �

, �

�, ��, where

�

�

�

�

�

��

�

�

�

iff � � � � �:

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

If we choose a valuation � on � such that � ��� � ��

, �

, �

�, and � ��� �

�, then in the model �

�

� �

�

� �

�, � ��� � ��
� � � we have that �

�

, �

,

�

�

�

�

� �

�

�

�

�

�, �

�

�

� �

�

�

�

� � �, �

� �

�

�

�� � ���, and �

� �

� �

�� �

�� �

�

�

�

�

�

�

1.3 Models and Frames

19

�

�

�� �

����.
Furthermore, �
, but
has no successors at all (we often call such points
why is it true at �
‘dead ends’ or ‘blind states’) it is vacuously true that � is true at all �-successors
of �

� is true at any dead end in any model.

. Indeed, any ‘boxed’ formula �

�. Now, it is clear that �

� is true at �

? Well, as �

and �

, �

, �

�

�

�

�

�

�

�

�

�

(ii) As a second example, let � be the SPO given in Figure 1.1, where � � ��,
�, �, �, �, �, ��, ��� and ��� means ‘� and � are different, and � can be divided
by �.’ Choose a valuation � on this frame such that � ��� � ��� �� ��� ���, and
�, and
� ��� � ���, and let �

� � �. Then �

�, �

�, �

� �

� � �

� �

� �

�

�

�

�

�

�

�

�

� �

�� �

�� �

��� �

���

�

�

�

�

�

(iii) Whereas a diamond � corresponds to making a single �-step in a model,
stacking diamonds one in front of the other corresponds to making a sequence
of �-steps through the model. The following deﬁned operators will sometimes
� for �
be useful: we write �
preceded by � occurrences of �. If we like, we can associate each of these deﬁned
�� is deﬁned
operators with its own accessibility relation. We do so inductively: �
���. Under this
to hold if � � �, and �
� iff there exists
deﬁnition, for any model � and state � in � we have �
a � such that �

� for � preceded by � occurrences of �, and �

�� is deﬁned to hold if �� ���� � �

�� and �

�.

� �

��

� �

�

�

�

�

�

�

�

�

�

�

(iv) The use of the word ‘world’ (or ‘possible world’) for the entities in �
derives from the reading of the basic modal language in which �
� is taken to mean
� to mean ‘necessarily �.’ Given this reading, the machinery of
‘possibly �,’ and �
frames, models, and satisfaction which we have deﬁned is essentially an attempt to
capture mathematically the view (often attributed to Leibniz) that necessity means
truth in all possible worlds, and that possibility means truth in some possible world.
The satisfaction deﬁnition stipulates that � and � check for truth not at all possi-
ble worlds (that is, at all elements of � ) but only at �-accessible possible worlds.
At ﬁrst sight this may seem a weakness of the satisfaction deﬁnition — but in fact,
it’s its greatest source of strength. The point is this: varying � is a mechanism
which gives us a ﬁrm mathematical grip on the pre-theoretical notion of access be-
tween possible worlds. For example, by stipulating that � � � � � we can allow
all worlds access to each other; this corresponds to the Leibnizian idea in its purest
form. Going to the other extreme, we might stipulate that no world has access to
any other. Between these extremes there is a wide range of options to explore.
Should interworld access be reﬂexive? Should it be transitive? What impact do
these choices have on the notions of necessity and possibility? For example, if we
demand symmetry, does this justify certain principles, or rule others out?

(v) Recall from Example 1.10 that in epistemic logic � is written as � and � �
is interpreted as ‘the agent knows that �.’ Under this interpretation, the intuitive
reading for the semantic clause governing � is: the agent knows � in a situation

�
20

1 Basic Concepts

�

� �) iff � is true in all situations � that are compatible with her
� (that is, �
� for all � such that ���). Thus, under this interpre-
knowledge (that is, if �
tation, � is to be thought of as a collection of situations, � is a relation which
models the idea of one situation being epistemically accessible from another, and
� governs the distribution of primitive information across situations. �

�

We now deﬁne frames, models and satisfaction for modal languages of arbitrary
similarity type.

Deﬁnition 1.23 Let � be a modal similarity type. A � -frame is a tuple � consisting
of the following ingredients:

(i) a non-empty set � ,
(ii) for each � � �, and each �-ary modal operator � in the similarity type � ,

an (� � �)-ary relation �

�.

So, again, frames are simply relational structures. If � contains just a ﬁnite number
� �; otherwise we
of modal operators �
� � ��. We turn such a frame into a
write �
model in exactly the same way we did for the basic modal language: by adding a
valuation. That is, a � -model is a pair �
� � � where � is a � -frame, and � is
a valuation with domain � and range � �� �, where � is the universe of �.

, . . . , �
or �

, we write �

�, . . . , �

� ��� ��

� ��� �

� ��� �

� �

��

�

�

�

�

�

�

�

�

�

�

�

The notion of a formula � being satisﬁed (or true) at a state � in a model �

�

�

�

�

��� ��

� � �� � � (notation: �

�) is deﬁned inductively. The clauses
for the atomic and Boolean cases are the same as for the basic modal language (see
Deﬁnition 1.20). As for the modal case, when ��

� � � we deﬁne

� �

�

�

�

� �

��

� � � � � �

�

� �

iff

for some �

, . . . , �

� � with �

�

��

� � � �

�

�

�

�

�

�

we have, for each �, �

�

� �

�

�

�

�

This is an obvious generalization of the way � is handled in the basic modal lan-
guage. Before going any further, the reader should formulate the satisfaction clause
for �

�.

� � � � � �

��

�

�

On the other hand, when ��
� is a unary relation and we deﬁne

�

� � � (that is, when � is a nullary modality) then

�

� � iff � � �

�

�

�

� �

That is, unlike other modalities, nullary modalities do not access other states. In
fact, their semantics is identical to that of the propositional variables, save that the
unary relations used to interpret them are not given by the valuation — rather, they
are part of the underlying frame.
As before, we often write �

� where � is clear from the
� for �
context. The concept of global truth (or universal truth) in a model is deﬁned

� �

�

�

1.3 Models and Frames

21

as for the basic modal language: it simply means truth at all states in the model.
And, as before, we sometimes extend the valuation � supplied by � to arbitrary
formulas. �

Example 1.24 (i) Let � be a similarity type with three unary operators ���, ���,
(that is, it is a
and ���. Then a � -frame has three binary relations �
labeled transition system with three labels). To give an example, let � , �
, �
and �
this formula is true at a state, if it has an �
an �
model �

be as in Figure 1.2, and consider the formula ���� � ����. Informally,
-successor satisfying � only if it has
�. Then the

-successor satisfying �. Let � be a valuation with � ��� � ��

���� � ����.

� � � has �

, and �

, �

� ��� �

� �

� �

� �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

(ii) Let � be a similarity type with a binary modal operator � and a ternary
� and a 4-ary rela-

operator �. Frames for this � contain a ternary relation �
tion �
. As an example, let � � ��� � � �� ��, �
���� � � �� ��� as in Figure 1.6, and consider a valuation � on this frame with
� � ���. Now, let � be the formula

� ���� � � ���, and �

� � ��� and � ��

� � ���, � ��

� ��

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

: �

�

���

: �

�

����

Fig. 1.6. A simple frame

�

�

�

�

�

�

��

� �

� �

� �

� � ���

�. An informal reading of � is ‘any triangle of which the
true at the other two vertices,
evaluation point is a vertex, and which has �
is true.’ The reader
can be expanded to a rectangle with a fourth point at which �
should be able to verify that � is true at �, and indeed at all other points, and hence
that it is globally true in the model. �

and �

�

�

�

Example 1.25 (Bidirectional Frames and Models) Recall from Example 1.14
that the basic temporal language has two unary operators � and � . Thus, according
to Deﬁnition 1.23, models for this language consist of a set bearing two binary re-
(the into-the-past relation), which
lations, �
are used to interpret � and � respectively. However, given the intended reading
of the operators, most such models are inappropriate: clearly we ought to insist on
(that is,
working with models based on frames in which �
frames in which ��� ��

(the into-the-future relation) and �

is the converse of �

���).

�� � �

�

�

�

�

Let us denote the converse of a relation � by �

�. We will call a frame of the

�

�

�
22

1 Basic Concepts

�

� a bidirectional frame, and a model built over such a frame a bidi-
form �� � �� �
rectional model. From now on, we will only interpret the basic temporal language
� � � is a bidirectional model
in bidirectional models. That is, if �
then:

� �� � �� �

�

�

� �

�

�

� �

�

� � iff
� � iff

�� ���� �

� �

��

�

�

�

�� ��

�� �

� �

���

�

�

But of course, once we’ve made this restriction, we don’t need to mention �
� ex-
plicitly any more: once � has been ﬁxed, its converse is ﬁxed too. That is, we are
free to interpret the basic temporal languages on frames �� � �� for the basic modal
language using the clauses

�

� �

�

�

� �

�

� � iff
� � iff

�� ���� �

� �

��

�

�

�� ���� �

� �

���

�

�

These clauses clearly capture a crucial part of the intended semantics: � looks
forward along �, and � looks backwards along �. Of course, our models will
only start looking genuinely temporal when we insist that � has further properties
(notably transitivity, to capture the ﬂow of time), but at least we have pinned down
the fundamental interaction between the two modalities. �

Example 1.26 (Regular Frames and Models) As explained in Example 1.15, the
language of PDL has an inﬁnite collection of diamonds, each indexed by a program
� built from basic programs using the constructors �, �, and �. Now, according to
Deﬁnition 1.23, a model for this language has the form

��� ��

�

� � is a program �� � ��

That is, a model is a labeled transition system together with a valuation. However,
given our reading of the PDL operators, most of these models are uninteresting. As
with the basic temporal language, we must insist on working with a class of models
that does justice to our intentions.

Now, there is no problem with the interpretation of the basic programs: any
binary relation can be regarded as a transition relation for a non-deterministic pro-
gram. Of course, if we were particularly interested in deterministic programs we
would insist that each basic program be interpreted by a partial function, but let us
ignore this possibility and turn to the key question: which relations should interpret
the structured modalities? Given our readings of �, � and �, as choice, composition,
and iteration, it is clear that we are only interested in relations constructed using
the following inductive clauses:

�

�

� � �

� � �

�

�

��

�

�

�

�

� � �

� � �

� �� ���� �� � �� ��

� �� � �

� �����

�

�

�

�

�

�

�

�

�

� ��

� �

�

� the reﬂexive transitive closure of �

� �

�

�

�

�

1.3 Models and Frames

23

These inductive clauses completely determine how each modality should be inter-
preted. Once the interpretation of the basic programs has been ﬁxed, the relation
corresponding to each complex program is ﬁxed too. This leads to the following
deﬁnition.

� � � � �� such that �

Suppose we have ﬁxed a set of basic programs. Let � be the smallest set of
programs containing the basic programs and all programs constructed over them
using the regular constructors �, � and �. Then a regular frame for � is a labeled
is an arbitrary binary relation
transition system ��� ��
for each basic program �, and for all complex programs �, �
is the binary relation
inductively constructed in accordance with the previous clauses. A regular model
for � is a model built over a regular frame; that is, a regular model is regular
frame together with a valuation. When working with the language of PDL over the
programs in �, we will only be interested in regular models for �, for these are
the models that capture the intended interpretation.

�

�

�

What about the � and � constructors? Clearly the intended reading of � demands
�. As for ?, it is clear that we want the following deﬁnition:

that �

� � �

� ��

�

�

��

�

�

� ���� �� � � � � and �

�

���

�

�

�

This is indeed the clause we want, but note that it is rather different from the others:
it is not a frame condition. Rather, in order to determine the relation �
, we need
information about the truth of the formula �, and this can only be provided at the
level of models. �

�

�

Example 1.27 (Arrow Models) Arrow frames were deﬁned in Example 1.8 and
the arrow language in Example 1.16. Given these deﬁnitions, it is clear how the
language of arrow logic should be interpreted. First, an arrow model is a structure
� ��� �� �� � � is an arrow frame and � is a valuation.

� � � such that �

� �

�

�

Then:

�

� �

�

�’

iff

� ��

�

� �

�

�� iff �

� �

� for some � with ����

�

�

� �

�

� � � iff �

� �

� and �

�

�

� �

� for some � and � with � ����

When � is a square frame �
(as deﬁned in Example 1.8), this works out as
follows. � now maps propositional variables to sets of pairs over � ; that is, to
binary relations. The truth deﬁnition can be rephrased as follows:

�

�

� ��

� �

�

�’

iff �

�

� �

�

�

�

�

�

�

� ��

� �

�

�� iff �

�

� ��

� �

�

�

�

�

�

�

�

�

� ��

� �

�

� � � iff �

�

� ��

� ��

�

� and �

� ��� �

� for some � � � �

�

�

�

�

�

�

Such situations can be represented pictorially in two ways. First, one could draw

24

1 Basic Concepts

the graph-like structures as given in Example 1.8. Alternatively, one could draw
a square model two-dimensionally, as in the picture below. It will be obvious that
the modal constant �’ holds precisely at the diagonal points and that �� is true at a
point iff � holds at its mirror image with respect to the diagonal. The formula � � �
holds at a point � iff we can draw a rectangle ���� such that: � lies on the vertical
line through �, � lies on the vertical line through �; and � lies on the diagonal.

�

�

�

�

�

�

�

�

�

�

�

�

�

� � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�’

�

�

�

�

�

��

�

�

�

�

�

�

�

�

�

�

Frames and validity

It is time to deﬁne one of the key concepts in modal logic. So far we have been
viewing modal languages as tools for talking about models. But models are com-
posite entities consisting of a frame (our underlying ontology) and contingent in-
formation (the valuation). We often want to ignore the effects of the valuation and
get a grip on the more fundamental level of frames. The concept of validity lets
us do this. A formula is valid on a frame if it is true at every state in every model
that can be built over the frame. In effect, this concept interprets modal formulas
on frames by abstracting away from the effects of particular valuations.

Deﬁnition 1.28 A formula � is valid at a state � in a frame � (notation: �
if � is true at � in every model �

�)
� � � based on �; � is valid in a frame � (notation:
�) if it is valid at every state in �. A formula � is valid on a class of frames
�) if it is valid on every frame � in � ; and it is valid (notation:
�) if it is valid on the class of all frames. The set of all formulas that are valid in

� (notation: � �

� �

�

�

�

�

�

a class of frames � is called the logic of � (notation: �

�).

�

Our deﬁnition of the logic of a frame class � (as the set of ‘all’ formulas that
are valid on �) is underspeciﬁed: we did not say which collection of proposition
letters � should be used to build formulas. But usually the precise form of this
collection is irrelevant for our purposes. On the few occasions in this book where
more precision is required, we will explicitly deal with the issue. (If the reader is

1.3 Models and Frames

25

����

� to be �� �

worried about this, he or she may just ﬁx a countable set � of proposition letters
and deﬁne �
As will become abundantly clear in the course of the book, validity differs from
truth in many ways. Here’s a simple example. When a formula � � � is true at a
point �, this means that that either � or � is true at � (the satisfaction deﬁnition
tells us so). On the other hand, if � � � is valid on a frame �, this does not mean
that either � or � is valid on � (� � �� is a simple counterexample).

��.)

�� � �� �

� �

�� is valid on all frames. To
Example 1.29 (i) The formula �
see this, take any frame � and state � in �, and let � be a valuation on �. We have
to show that if �
�. So assume that
�� � ��. Then, by deﬁnition there is a state � such that ��� and
�. Hence either

� � � then either �

� � �. But, if �

�� � ��, then �

� or �

�� � �� � �

� � �� �

� � �� �

� � �� �

� � �� �

� �

� �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

� or �

�

�

�

�

�

�. Either way, �

�

�

� �

�.

�

(ii) The formula ��

� is not valid on all frames. To see this we need to
ﬁnd a frame �, a state � in �, and a valuation on � that falsiﬁes the formula at �.
So let � be a three-point frame with universe ��� �� �� and relation ���� ��� ��� ���.
�, but
Let � be any valuation on � such that � ��� � ���. Then �

� � �� �

� �

��

�

�

�

�

�

�

�

� � �� � �

� since 0 is not related to 2.
(iii) But there is a class of frames on which ��

the class
of transitive frames. To see this, take any transitive frame � and state � in �,
�, then
and let � be a valuation on �. We have to show that if �
�. Then by deﬁnition there are
�. But as � is transitive, it

�. So assume that �

� is valid:

� � �� �

� � �� �

� � �� �

� � �� �

� �

��

��

�

�

�

�

�

�

�

�

�

�

�

states � and � such that ��� and ��� and �
follows that ���, hence �

�.

� � �� �

�

�

�

(iv) As the previous example suggests, when additional constraints are imposed
on frames, more formulas may become valid. For example, consider the frame
depicted in Figure 1.2. On this frame the formula ���� � ���� is not valid; a coun-
�. Now, consider a frame satisfying
termodel is obtained by putting � ��� � ��
the condition �

; an example is depicted in Figure 1.7.

� �

�

�

�

�

�

�

�

�

�

�

�

�

�

Fig. 1.7. A frame satisfying �

�

�

�

�

.

��

On this frame it is impossible to refute the formula ���� � ���� at �, because a
�� and � true at �, but
refutation would require the existence of a point � with �
.
not �

��; but such points are forbidden when we insist that �

� �

�

�

�

�

This is a completely general point: in every frame � of the appropriate similarity
, then ���� � ���� is valid in �. More-

type, if � satisﬁes the condition �

� �

�

�

26

1 Basic Concepts

over, the converse to this statement also holds: whenever ���� � ���� is valid on
a given frame �, then the frame must satisfy the condition �
. To use the
terminology we will introduce in Chapter 3, the formula ���� � ���� deﬁnes the
property that �

.

� �

� �

�

�

�

�

(v) When interpreting the basic temporal language (see Example 1.25) we ob-
� were uninteresting given the
served that arbitrary frames of the form ��� �
intended interpretation of � and � , and we insisted on interpreting them using a
relation � and its converse. Interestingly, there is a sense in which the basic tempo-
is
ral language itself is strong enough to enforce the condition that the relation �
: such frames are precisely the ones which validate
the converse of the relation �
both the formulas � � �� � and � � � � �; see Exercise 3.1.1.

� �

�

�

�

�

(vi) The formula � � � � � � is not valid on all frames. To see this we need
� �� � ��, a state � in �, and a valuation on � that falsiﬁes
to ﬁnd a frame �
this formula at �. So let � � ��� ��, and let � be the relation ���� ���. Let
� �, but obviously
� be a valuation such that � ��� � ���. Then �

� � �� �

�

�

�

� � �� � �

�

�

� � �.

(vii) But there is a frame on which � � � � � � is valid. As the universe of the
frame take the set of all rational numbers �, and let the frame relation be the usual
�-ordering on �. To show that � � � � � � is valid on this frame, take any point
� �; we have to show that
� in it, and any valuation � such that �
�.
Because we are working on the rationals, there must be an � with � � � and � � �
(for example, �� � �

� � �. But this is easy: as �

� �, it follows that �

� �, there exists a �

� such that � � �

���). As �

� and �

� � �.

� �� � �� �

�

�

�

�

�

�

�

�

�

�

�

(viii) The special conditions demanded of PDL models also give rise to validities.

For example, ��

� �

�� � ��

���

�� is valid on any frame such that �

�

� �

�

� � �

�, and in fact the converse is also true. The reader is asked to prove this

�

�

�

�

�

�

�

�

�

in Exercise 3.1.2.

�

arrow frame �
valuation on �

(ix) In our last example we consider arrow logic. We claim that in any square
, the formula ��� � �� � �� � �� is valid. For, let � be a
, and suppose that for some pair of points �� � in � , we have
� � �, and hence,
�.
��. This in turn

��� � ��. It follows that �

there must be a � � � for which �
But then we have �
implies that �

�� � ��. �

�� and �

� and �

� � �� ��� ��

� � �� ��� ��

� � �� �� � ��

� � �� ��� ��

� � �� ��� ��

� � �� �� � ��

� � �� ��� ��

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

Exercises for Section 1.3
1.3.1 Show that when evaluating a formula � in a model, the only relevant information in
the valuation is the assignments it makes to the propositional letters actually occurring in
�. More precisely, let � be a frame, and � and �

� be two valuations on � such that �

�

�

� �

�

�

� for all proposition letters � in �. Show that �

�. Work in the
basic modal language. Do this exercise by induction on the number of connectives in � (or

� iff �

� �

� �

�

�

�

�

�

�

�

�

�

1.4 General Frames

27

as we usually put it, by induction on �). (If you are unsure how to do this, glance ahead to
Proposition 2.3 where such a proof is given in detail.)

1.3.2 Let �
similarity type with two diamonds �
the set of strings of �s and �s, and the relations are deﬁned by

� and �

and �

� be the following frames for a modal
. Here � is the set of natural numbers, � is

� �

� �

� �

� �

� �

� �

�

�

�

�

�

�

�

�

��

�

�

��

�

�

��

�

�

��

�

�

�

�

�

iff
iff � � ��
iff
iff

�

�

�

� �

�

�

�

�

�

� or �

� is a proper initial segment of ��

Which of the following formulas are valid on � and �, respectively?

�

�

�

�

�

� �

�

�

�

�

�

�

�

�

�

�

�

�

� �

�

�

�

�

�

�

�

�,
�,

�

�

�

�

�

�

�

�

�

�

�

� � �

�

�

� �

�

�

� �

�

�

�

�

�

�

�

�

�

�

�

�

�

��,

�

�

�

(a) �
(b) �
(c) �
(d) �
(e) �
(f) �
(g) �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�,
�,
�,
�.

1.3.3 Consider the basic temporal language and the frames �
(the integer, rational, and real numbers, respectively, all ordered by the usual less-than
� �, and A� to abbreviate
relation �). In this exercise we use E� to abbreviate � �

� and �

�, �

� �

� �

� �

�

�

�

�

�

�

�

� �

�

�

�

��. Which of the following formulas are valid on these frames?

(a) ���
(b) �
(c) �E�

�

�

�,

�

� �

� �

� � �,

� E�

� A�

�

�

� �

�

� � A��

�

�

�

�

�

�� � E�

� �

�

�

�

�.

�

1.3.4 Show that every formula that has the form of a propositional tautology is valid.
Further, show that �

� is valid.

� � �

�

�

�

�

�

�

�

�

�

1.3.5 Show that each of the following formulas is not valid by constructing a frame �

�

� that refutes it.

�

�� �

�,

(a) �
(b) �
(c) �
(d) ��

�

�

�

�

�,
�,

��

�

�

��

�.

Find, for each of these formulas, a non-empty class of frames on which it is valid.

1.3.6 Show that the arrow formulas �
any square.

� �

�

� � �

�

� �

�

�

�

�

� and �’ �

�

�

� are valid in

1.4 General Frames

At the level of models the fundamental concept is satisfaction. This is a relatively
simple concept involving only a frame and a single valuation. By ascending to the

28

1 Basic Concepts

level of frames we get a deeper grip on relational structures — but there is a price to
pay. Validity lacks the concrete character of satisfaction, for it is deﬁned in terms of
all valuations on a frame. However there is an intermediate level: a general frame
� �� is a frame � together with a restricted, but suitably well-behaved collection

�

�

� of admissible valuations.

�

General frames are useful for at least two reasons. First, there may be appli-
cation driven motivations to exclude certain valuations. For instance, if we were
� �� to model the temporal distribution of outputs from a computational
using �
device, it would be unreasonable to let valuations assign non recursively enumer-
able sets to propositional variables. But perhaps the most important reason to work
with general frames is that they support a notion of validity that is mathematically
simpler than the frame-based one, without losing too many of the concrete prop-
erties that make models so easy to work with. This ‘simpler behavior’ will only
really become apparent when we discuss the algebraic perspective on complete-
ness theory in Chapter 5. It will turn out that there is a fundamental and universal
completeness result for general frame validity, something that the frame semantics
lacks. Moreover, we will discover that general frames are essentially a set-theoretic
representation of boolean algebras with operators. Thus, the � in ��� �� �� stands
not only for Admissible, but also for Algebra.

So what is a ‘suitably well-behaved collection of valuations’? It simply means a
collection of valuations closed under the set-theoretic operations corresponding to
our connectives and modal operators. Now, fairly obviously, the boolean connec-
tives correspond to the boolean operations of union, relative complement, and so
on — but what operations on sets do modalities correspond to? Here is the answer.
Let us ﬁrst consider the basic modal similarity type with one diamond. Given a

frame �

� ��� ��, let �

� be the following operation on the power set of � :

�� � � �� � � � ��� for some � � � ��

�

�

Think of �
sponds to the diamond in the sense that for any valuation � and any formula �:

�� � as the set of states that ‘see’ a state in �. This operation corre-

�

Moving to the general case, we obtain the following deﬁnition.

� �

�� � �

�� �����

�

�

Deﬁnition 1.30 Let � be a modal similarity type, and �
� � we deﬁne the following function �
For �

� on the power set of � :

� ��� �

�

��

�

�

a � -frame.

�

��

� � � � � �

�

�

�

� � �� � � � there are �

, . . . , �

� � such that

�

�

�

��

� � � �

�

and �

� �

�

for all � � �� � � � � �.� �

�

�

�

�

Example 1.31 Let � be the converse operator of arrow logic, and consider a

1.4 General Frames

29

square frame �

. Note that �

�

is the following operation:

�

�

�� � � �� � �

�

�

� ��� for some � � � ��

But by the rather special nature of � this boils down to

�

�� � � ���

� �

� � �

� �

� �

�

and �

for some ��

� �

� �

� � � ��

�

�

�

�

�

�

�

�

�

� ���

� �

� � �

� ��

� �

� � � ��

�

�

�

�

�

In other words, �

�� � is nothing but the converse of the binary relation �. �

�

Deﬁnition 1.32 (General Frames) Let � be a modal similarity type. A general � -
frame is a pair �
is a � -frame, and � is a non-empty
collection of subsets of � closed under the following operations:

� �� where �

� ��� �

��

�

�

�

�

(i) union: if �, � � � then � � � � �.
(ii) relative complement: if � � �, then � � � � �.
(iii) modal operations: if �

� �, then �

, . . . , �

�

��

� � � � � �

� � � for all

� � .

�

�

�

�

�

A model based on a general frame is a triple �
� �� is a general
frame and � is a valuation satisfying the constraint that for each proposition letter
�, � ��� is an element of �. Valuations satisfying this constraint are called admis-
sible for �

� �� � � where �

� ��. �

�

�

�

It follows immediately from the ﬁrst two clauses of the deﬁnition that both the
empty set and the universe of a general frame are always admissible. Note that
can be regarded as a general frame where
an ordinary frame �
� � � �� � (that is, a general frame in which all valuations are admissible). Also,
note that if a valuation � is admissible for a general frame �
� ��, then the closure
conditions listed in Deﬁnition 1.32 guarantee that � ��� � �, for all formulas
�. In short, a set of admissible valuations � is a ‘logically closed’ collection of
information assignments.

� ��� �

��

�

�

�

�

Deﬁnition 1.33 A formula � is valid at a state � in a general frame �
tation: �

�) if � is true at � in every admissible model �

� ��� �

�

�

�

�

�

� ��; and � is valid in a general frame �
at every state in every admissible model �

�

� �� (notation: �
� ��.
� �� � � on �

�

�

�

� ��

�

�

� �� (no-
� �� � � on
�) if � is true

A formula � is valid on a class of general frames � (notation: � �

valid on every general frame �
general frames we say that it is g-valid and write �
(see Exercise 4.1.1) that a formula � is valid if and only if it is g-valid. �

�) if it is
� �� in �. Finally, if � is valid on the class of all
�. We will learn in Chapter 4

�

�

30

1 Basic Concepts

Clearly, for any frame �, if �
ments � on �, we have �
counterexample that will be useful in Chapter 4.

� ��

�

�

�

� then for any collection of admissible assign-
� too. The converse does not hold. Here is a

�. It is easy to see
Example 1.34 Consider the McKinsey formula, ��
that the McKinsey formula is not valid on the frame �
� ��, for we obtain a coun-
termodel by choosing a valuation for � that lets the truth value of � alternate in-
ﬁnitely often (for instance, by letting � ��� be the collection of even numbers).

� �

��

�

However there is a general frame based on �

� �� in which the McKinsey for-
mula is valid. First some terminology: a set is co-ﬁnite if its complement is ﬁnite.
� �� ��, where � is the collection of all
Now consider the general frame �
ﬁnite and co-ﬁnite sets. We leave it as an exercise to show that � satisﬁes all the
constraints of Deﬁnition 1.32; see Exercise 1.4.5.

� �

�

�

To see that the McKinsey formula is indeed valid on �, let � be an admissible
�, then � ��� must be co-ﬁnite (why?),
�,

valuation, and let � �
hence for some � every state � � � is in � ���. But this means that �
as required. �

�. If �

� � �� �

� � �� �

��

��

�

�

�

�

Although we will make an important comment about general frames in Section 3.2,
and use them to help prove an incompleteness result in Section 4.4, we will not re-
ally be in a position to grasp their signiﬁcance until Chapter 5, when we introduce
boolean algebras with operators. Until then, we will concentrate on modal lan-
guages as tools for talking about models and frames.

Exercises for Section 1.4
�, an operation �
1.4.1 Deﬁne, analogous to �
for an arbitrary modal formula � and an arbitrary valuation � we have that �
�. Extend this deﬁnition to the dual of a polyadic modal operator.

�

�

�

�

� on the power set of a frame such that

�

�

�

�� �

�

�

1.4.2 Consider the basic modal formula �

�

�

�.

�

(a) Construct a frame �

� �

�� �

� and a general frame �

� �

�

� �

� such that �

�

�

�

�

�, but �

�

�

�

�

�

�.

�

(b) Construct a general frame �

� and a valuation � on � such that �

�

� �

�

� �

�

� �

�

�

�

�, but �

�

�

� �

�

�

�

�

�

�

�.

1.4.3 Show that if � is any collection of valuations over some frame �, then there is a
smallest general frame �
�. (‘Smallest’ means that for any general
� such that �
frame �

� such that �
�.)

�, �

� �

� �

�

�

�

�

�

�

�

�

1.4.4 Show that for square arrow frames, the operation �
two binary relations. What is �

�’?

is nothing but composition of

�

1.4.5 Consider the basic modal language, and the general frame �
is the collection of all ﬁnite and co-ﬁnite sets. Show that � is a general frame.

� �

�

� �� �

�, where �

�
1.5 Modal Consequence Relations

31

1.4.6 Consider the structure �
subsets of �, and � is deﬁned by

� �

�

� �� �

� where � is the collection of ﬁnite and coﬁnite

� �

�

�

iff �

�

�

�

�

and �

�

�

�

�

and �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

If � is the accessibility relation of a dyadic modal operator, show that � is a general frame.

1.4.7 Let �

� �

�

� �

� be some modal model. Prove that the structure

�

�

�

� �

�

�

�

�

� is a formula ��

is a general frame.

1.5 Modal Consequence Relations
While the idea of validity in frames (and indeed, validity in general frames) gives
rise to logically interesting formulas, so far we have said nothing about what logical
consequence might mean for modal languages. That is, we have not explained what
it means for a set of modal formulas � to logically entail a modal formula �.

This we will now do. In fact, we will introduce two families of consequence
relations: a local one and a global one. Both families will be deﬁned semantically;
that is, in terms of classes of structures. We will deﬁne these relations for all three
kinds of structures we have introduced, though in practice we will be primarily
interested in semantic consequence over frames. Before going further, a piece of
terminology. If � is a class of models, then a model from � is simply a model � in
�. On the other hand, if � is a class of frames (or a class of general frames) then a
model from � is a model based on a frame (general frame) in �.

What is a modally reasonable notion of logical consequence? Two things are
fairly clear. First, it seems sensible to hold on to the familiar idea that a relation
of semantic consequence holds when the truth of the premises guarantees the truth
of the conclusion. Second, it should be clear that the inferences we are entitled to
draw will depend on the class of structures we are working with. (For example,
different inferences will be legitimate on transitive and intransitive frames.) Thus
our deﬁnition of consequence will have to be parametric: it must make reference
to a class of structures S.

Here’s the standard way of meeting these requirements. Suppose we are working
with a class of structures S. Then, for a formula � (the conclusion) to be a logical
consequence of � (the premises) we should insist that whenever � is true at some
point in some model from �, then � should also be true in that same model at the
same point. In short, this deﬁnition demands that the maintenance of truth should
be guaranteed point to point or locally.

Deﬁnition 1.35 (Local Semantic Consequence) Let � be a similarity type, and
let � be a class of structures of type � (that is a class of models, a class of frames,

32

1 Basic Concepts

or a class of general frames of this type). Let � and � be a set of formulas and
a single formula from a language of type � . We say that � is a local semantic
consequence of � over � (notation: �
�) if for all models � from �, and all
points � in �, if �

� then �

�� �

� �

� �

�

�

�

�

Example 1.36 Suppose that we are working with ����, the class of transitive
frames. Then:

��

�

�

�

��

��

����

On the other hand, �
class of all frames. �

� is not a local semantic consequence of �

��

�� over the

Local consequence is the notion of logical entailment explored in this book, but it
is by no means the only possibility. Here’s an obvious variant.

Deﬁnition 1.37 (Global Semantic Consequence) Let � , �, � and � be as in
Deﬁnition 1.35. We say that � is a global semantic consequence of � over �
(notation: �
�) if and only if for all structures � in �, if �
(Here, depending on the kind of structures � contains, � denotes either validity in
a frame, validity in a general frame, or global truth in a model.) �

� then �

��

�

�

�

�

�

Again, this deﬁnition hinges on the idea that premises guarantee conclusions, but
here the guarantee covers global notions of correctness.

Example 1.38 The local and global consequence relations are different. Consider
the formulas � and �
� — indeed,
that this entailment should not hold is pretty much the essence of locality. On the
other hand, suppose that we consider a model � where � is globally true. Then �
certainly holds at all successors of all states, so �

�. It is easy to see that � does not locally imply �

�, and so �

�. �

�

�

�

�

�

Nonetheless, there is a systematic connection between the two consequence rela-
tions, as the reader is asked to show in Exercise 1.5.3.

Exercises for Section 1.5
1.5.1 Let � be a class of frames for the basic modal similarity type, and let �
the class of models based on a frame in �. Prove that �
(every point has a predecessor).

� iff �

�

�

�

�

�

�

�

� denote

�

�

�� �

�

� ���

�

Does this equivalence hold as well if we work with �

instead?

�

�

1.5.2 Let M denote the class of all models, and � the class of all frames. Show that if

�

�

�

� then �

�

�

�, but that the converse is false.

�

�

1.5.3 Let � be a set of formulas in the basic modal language, and let � denote the class of
all frames. Show that �

� iff �

�.

� � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

1.6 Normal Modal Logics

33

1.5.4 Again, let � denote the class of all frames. Show that the local consequence relation
�, but the global one does not.
� iff �
does have the deduction theorem: �
However, show that on the class ���� of transitive frames we have that �
� iff

�

�

�

�

�

�

�

�

����

�

�

�.

����

1.6 Normal Modal Logics

Till now our discussion has been largely semantic; but logic has an important syn-
tactic dimension, and our discussion raises some obvious questions. Suppose we
are interested in a certain class of frames F: are there syntactic mechanisms capable
of generating �
�, the formulas valid on F? And are such mechanisms capable of
coping with the associated semantic consequence relation? The modal logician’s
response to such questions is embodied in the concept of a normal modal logic.

A normal modal logic is simply a set of formulas satisfying certain syntactic clo-
sure conditions. Which conditions? We will work towards the answer by deﬁning a
Hilbert-style axiom system called K. K is the ‘minimal’ (or ‘weakest’) system for
reasoning about frames; stronger systems are obtained by adding extra axioms. We
discuss K in some detail, and then, at the end of the section, deﬁne normal modal
logics. By then, the reader will be in a position to see that the deﬁnition is a more-
or-less immediate abstraction from what is involved in Hilbert-style approaches to
modal proof theory. We will work in the basic modal language.

Deﬁnition 1.39 A K-proof is a ﬁnite sequence of formulas, each of which is an
axiom, or follows from one or more earlier items in the sequence by applying a
rule of proof . The axioms of K are all instances of propositional tautologies plus:

(K)
(Dual) �

�

� � �

�

��.

�� � �� � �

�

�

� �

��

The rules of proof of K are:

� Modus ponens: given � and � � �, prove �.
� Uniform substitution: given �, prove �, where � is obtained from � by uniformly

replacing proposition letters in � by arbitrary formulas.

� Generalization: given �, prove �

�.

A formula � is K-provable if it occurs as the last item of some K-proof, and if this
is the case we write �

�. �

�

Some comments. Tautologies may contain modalities (for example, �
� is a
tautology, as it has the same form as � � ��). As tautologies are valid on all frames
(Exercise 1.3.4), they are a safe starting point for modal reasoning. Our decision
to add all propositional tautologies as axioms is an example of axiomatic overkill;

� � �

�

34

1 Basic Concepts

we could have chosen a small set of tautologies capable of generating the rest via
the rules of proof, but this reﬁnement is of little interest for our purposes.

�

� � � then �

points we should make. First, modus ponens preserves validity. That is, if �

Modus ponens is probably familiar to all our readers, but there are two important
� and
�. Given that we want to reason about frames, this property is
crucial. Note, however, that modus ponens also preserves two further properties,
�) and satisﬁability
namely global truth (if �
�). That is, modus ponens is not
(if �
only a correct rule for reasoning about frames, it is also a correct rule for reasoning
about models, both globally and locally.

� and �
� � � then �

� � � then �

� and �

� �

� �

� �

�

�

�

�

�

�

Uniform substitution should also be familiar. It mirrors the fact that validity ab-
stracts away from the effects of particular assignments: if a formula is valid, this
cannot be because of the particular value its propositional symbols have, thus we
should be free to uniformly replace these symbols with any other formula what-
soever. And indeed, as the reader should check, uniform substitution preserves
validity. Note, however, that it does not preserve either global truth or satisﬁabil-
ity. (For example, � is obtainable from � by uniform substitution, but just because
� is globally true in some model, it does not follow that � is too!) In short, uniform
substitution is strictly a tool for generating new validities from old.

That’s the classical core of our Hilbert system, so let’s turn to the the genuinely
modal axioms and rules of proof. First the axioms. The K axiom is the fundamental
one. It is clearly valid (as the reader who has not done Exercise 1.3.4 should now
check) but why is it a useful addition to our Hilbert system?

�

� �

�� � �� (a boxed formula) into �

K is sometimes called the distribution axiom, and is important because it lets us
� (an implication). This
transform �
box-over-arrow distribution enables further purely propositional reasoning to take
�, and have constructed a
place. For example, suppose we are trying to prove �
�. If we could apply modus
proof sequence containing both �
�. And this is what
ponens under the scope of the box, we would have proved �
��,
distribution lets us do: as K contains the axiom �
��. But then a
by uniform substitution we can prove �
� as
ﬁrst application of modus ponens proves �
desired.

�, and a second proves �

�� � �� and �

�� � �� � �

�� � �� � �

� �

� �

� �

�

�

�

�

�

The Dual axiom obviously reﬂects the duality of � and �; nonetheless, readers
familiar with other discussions of K (many of which have K as the sole modal
axiom) may be surprised at its inclusion. Do we really need it? Yes, we do. In this
book, � is primitive and � is an abbreviation. Thus our K axiom is really shorthand
���. We need a way to maneuver around
for �
these negations, and this is the syntactic role that Dual plays. (Incidentally had we
chosen � as our primitive operator, Dual would not have been required.) We prefer
working with a primitive � (apart from anything else, it is more convenient for the

��� � �� � ��

�� � �

�

�

�

1.6 Normal Modal Logics

35

algebraic work of Chapter 5) and do not mind adding Dual as an extra axiom. Dual,
of course, is valid.

It only remains to discuss the modal rule of proof: generalization (another com-
mon name for it is necessitation). Generalization ‘modalizes’ provable formulas by
stacking boxes in front. Roughly speaking, while the K axiom lets us apply classi-
cal reasoning inside modal contexts, necessitation creates new modal contexts for
us to work with; modal proofs arise from the interplay of these two mechanisms.

Note that generalization preserves validity: if it is impossible to falsify �, then
obviously we will never be able to falsify � at any accessible state! Similarly,
generalization preserves global truth. But it does not preserve satisfaction:
just
because � is true in some state, we cannot conclude that � is true at all accessible
states.

� is the minimal modal Hilbert system in the following sense. As we have
seen, its axioms are all valid, and all three rules of inference preserve validity,
hence all K-provable formulas are valid. (To use the terminology introduced in
Deﬁnition 4.9, K is sound with respect to the class of all frames.) Moreover, as we
will prove in Theorem 4.23, the converse is also true: if a basic modal formula is
valid, then it is K-provable. (That is, K is complete with respect to the class of all
frames.) In short, K generates precisely the valid formulas.

�� � �� is valid on any frame, so
Example 1.40 The formula �
it should be K-provable. And indeed, it is. To see this, consider the following
sequence of formulas:

�� �

� �

�

�

�

�� � � � �� � �� � ���

�� �

�� � �� � �� � ����

�

�� �

�� � �� � �

� �

��

�

�

�

Tautology
Generalization: 1
K axiom

�� �

�� � �� � �� � ��� � �

� �

�� � �� � ����

�

�

�

�� �

� �

�� � �� � ���

�

�

�� �

�� � �� � ��� � �

� �

�

�

�

�� �

� � �

� �

�� � ���

�

�

�

�� � �

� �

�� �

�� � ��

�

�

�

Uniform Substitution: 3
Modus Ponens: 2, 4

�� � ��� Uniform Substitution: 3
Propositional Logic: 5, 6
Propositional Logic: 7

Strictly speaking, this sequence is not a K-proof — it is a subsequence of the proof
consisting of the most important items. The annotations in the right-hand column
should be self-explanatory; for example ‘Modus Ponens: 2, 4’ labels the formula
obtained from the second and fourth formulas in the sequence by applying modus
ponens. To obtain the full proof, ﬁll in the items that lead from line 6 to 8. �

Remark 1.41 Warning: there is a pitfall that is very easy to fall into if you are used
to working with natural deduction systems: we cannot freely make and discharge

36

1 Basic Concepts

assumptions in the Hilbert system K. The following ‘proof’ shows what can go
wrong if we do:

�� �

��

�

�

�� � �

�

Assumption
Generalization: 1
� Discharge assumption

�

�! This is obviously wrong: this formula is not valid,
So we have ‘proved’ � �
hence it is not K-provable. And it should be clear where we have gone wrong:
we cannot use assumptions as input to generalization, for, as we have already re-
marked, this rule does not preserve satisﬁability. Generalization is there to enable
us to generate new validities from old. It is not a local rule of inference. �

For many purposes, K is too weak. If we are interested in transitive frames, we
would like a proof system which reﬂects this. For example, we know that ��

� �

� is valid on all transitive frames, so we would want a proof system that generates

�

this formula; K does not do this, for ��

� �

� is not valid on all frames.

�

But we can extend K to cope with many such restrictions by adding extra ax-
� as an axiom, we obtain
ioms. For example, if we enrich K by adding ��
the Hilbert-system called K4. As we will show in Theorem 4.27, K4 is sound and
complete with respect to the class of all transitive frames (that is, it generates pre-
cisely the formulas valid on transitive frames). More generally, given any set of
modal formulas � , we are free to add them as extra axioms to K, thus forming the
axiom system ��. As we will learn in Chapter 4, in many important cases it is
possible to characterize such extensions in terms of frame validity.

� �

�

One ﬁnal issue remains to be discussed: do such axiomatic extensions of K give
us a grip on semantic consequence, and in particular, the local semantic conse-
quence relation over classes of frames (see Deﬁnition 1.35)?

In many important cases they do. Here’s the basic idea. Suppose we are inter-
ested in transitive frames, and are working with K4. We capture the notion of local
consequence over transitive frames in K4 as follows. Let � be a set of formulas,
and � a formula. Then we say that � is a local syntactic consequence of � in K4
� of �
�) if and only if there is some ﬁnite subset ��
(notation: � �
such that �

� �. In Theorem 4.27 we will show that

� � � � � �

� � � � � �

��

��

�

�

�

�

�

� �

��

� iff �

�

����

��

where �
���� denotes local semantic consequence over transitive frames. In short,
we have reduced the local semantic consequence relation over transitive frames to
provability in K4.

Deﬁnition 1.42 (Normal Modal Logics) A normal modal logic � is a set of for-
��,
mulas that contains all tautologies, �

��, and �

�� � �� � �

� � �

� �

�

�

�

1.6 Normal Modal Logics

37

and that is closed under modus ponens, uniform substitution and generalization.
We call the smallest normal modal logic K. �

This deﬁnition is a direct abstraction from the ideas underlying modal Hilbert sys-
tems. It throws away all talk of proof sequences and concentrates on what is really
essential: the presence of axioms and closure under the rules of proof.

We will rarely mention Hilbert systems again: we prefer to work with the more
abstract notion of normal modal logics. For a start, although the two approaches
are equivalent (see Exercise 1.6.6), it is simpler to work with the set-theoretical
notion of membership than with proof sequences. More importantly, in Chapters 4
and 5 we will prove results that link the semantic and syntactic perspectives on
modal logic. These results will hold for any set of formulas fulﬁlling the normality
requirements. Such a set might be the formulas generated by a Hilbert-style proof
system — but it could just as well be the formulas provable in a natural-deduction
system, a sequent system, a tableaux system, or a display calculus. Finally, the
concept of a normal modal logic makes good semantic sense: for any class of
frames �, we have that �
�, the set of formulas valid on �, is a normal modal logic;
see Exercise 1.6.7.

Exercises for Section 1.6
1.6.1 Give K-proofs of �

�

�

�

�

�

� �

�

�

�

�

�

� and �

�

�

�

�

�

�

� � �

�

�

�

�.

� be the ‘demodalized’ version of a modal formula �; that is, �

1.6.2 Let �
from � by simply erasing all diamonds. Prove that �
ever � is K-provable. Conclude that not every modal formula is K-provable.

� is obtained
� is a propositional tautology when-

1.6.3 The axiom system known as S4 is obtained by adding the axiom �
� to K4.
�; that is, show that S4 does not prove this formula. (Hint: ﬁnd an
Show that ��
appropriate class of frames for which S4 is sound.) If we add this formula as an axiom to
S4 we obtain the system called ��. Give an S5-proof of ��

�.

��

�

�

�

��

�

�

�

�

1.6.4 Try adapting K to obtain a minimal Hilbert system for the basic temporal language.
Does your system cope with the fact that we only interpret this language on bidirectional
frames? Then try and deﬁne a minimal Hilbert system for the language of propositional
dynamic logic.

1.6.5 This exercise is only for readers who like syntactical manipulations and have a lot
of time to spare. KL is the axiomatization obtained by adding the L¨ob formula �

�

�

�

�

�

� �

�

� as an extra axiom to K. Try and ﬁnd a KL proof of �

�

��

�

�. That is, show

that KL � KL4.

1.6.6 In Chapter 4 we will use �� to denote the smallest normal modal logic containing
� ; the point of the present exercise is to relate this notation to our discussion of Hilbert
systems. So (as discussed above) suppose we form the axiom system �� by adding as
axioms all the formulas in � to K. Show that the Hilbert system �� proves precisely the
formulas contained in the normal modal logic ��.

38

1 Basic Concepts

1.6.7 Let � be a class of frames. Show that �

� is a normal modal logic.

1.7 Historical Overview

The ideas introduced in this chapter have a long history. They evolved as responses
to particular problems and challenges, and knowing something of the context in
which they arose will make it easier to appreciate why they are considered im-
portant, and the way they will be developed in subsequent chapters. Some of the
discussion that follows may not be completely accessible at this stage. If so, don’t
worry. Just note the main points, and try again once you have explored the chapters
that follow.

We ﬁnd it useful to distinguish three phases in the development of modal logic:
the syntactic era, the classical era, and the modern era. Roughly speaking, most of
the ideas introduced in this chapter stem from the classical era, and the remainder
of the book will explore them from the point of view of the modern era.

The syntactic era (1918–1959)

We have opted for 1918, the year that C.I. Lewis published his Survey of Sym-
bolic Logic [306], as the birth of modal logic as a mathematical discipline. Lewis
was certainly not the ﬁrst to consider modal reasoning, indeed he was not even the
ﬁrst to construct symbolic systems for this purpose: Hugh MacColl, who explored
the consequences of enriching propositional logic with operators � (‘it is certain
that’) and � (‘it is impossible that’) seems to have been the ﬁrst to do that (see his
book Symbolic Logic and its Applications [312], and for an overview of his work,
see [373]). But MacColl’s work is ﬁrmly rooted in the 19-th century algebraic
tradition of logic (well-known names in this tradition include Boole, De Morgan,
Jevons, Peirce, Schr¨oder, and Venn), and linking MacColl’s contributions to con-
temporary concerns is a non-trivial scholarly task. The link between Lewis’s work
and contemporary modal logic is more straightforward.

In his 1918 book, Lewis extended propositional calculus with a unary modality
I (‘it is impossible that’) and deﬁned the binary modality � � � (� strictly implies
�) to be I�� � ���. Strict implication was meant to capture the notion of logical
entailment, and Lewis presented a �-based axiom system. Lewis and Langford’s
joint book Symbolic Logic [307], published in 1932, contains a more detailed de-
velopment of Lewis’ ideas. Here � (‘it is possible that’) is primitive and � � �
is deﬁned to be �
�� � ���. Five axiom systems of ascending strength, S1–S5,
are discussed; S3 is equivalent to Lewis’ system of 1918, and only S4 and S5 are
normal modal logics. Lewis’ work sparked interest in the idea of ‘modalizing’
propositional logic, and there were many attempts to axiomatize such concepts as

�

1.7 Historical Overview

39

obligation, belief and knowledge. Von Wright’s monograph An Essay in Modal
Logic [456] is an important example of this type of work.

But in important respects, Lewis’ work seems strange to modern eyes. For a
start, his axiomatic systems are not modular. Instead of extending a base system of
propositional logic with speciﬁcally modal axioms (as we did in this chapter when
we deﬁned K), Lewis deﬁnes his axioms directly in terms of �. The modular
approach to modal Hilbert systems is due to Kurt G¨odel. G¨odel [181] showed
that (propositional) intuitionistic logic could be translated into S4 in a theorem-
preserving way. However instead of using the Lewis and Langford axiomatization,
G¨odel took � as primitive and formulated S4 in the way that has become standard:
he enriched a standard system for classical propositional logic with the rule of
�).
generalization, the � axiom, and the additional axioms (�
But the fundamental difference between current modal logic and the work of
Lewis and his contemporaries is that the latter is essentially syntactic. Propositional
logic is enriched with some new modality. By considering various axioms, the
logician tries to pin down the logic of the intended interpretation. This simple view
of logical modeling has its attractions, but is open to serious objections. First, there
are technical difﬁculties. Suppose we have several rival axiomatizations of some
concept. Forget for now the problem of judging which is the best, for there is a
more basic difﬁculty: how can we tell if they are really different? If we only have
access to syntactic ideas, proving that two Hilbert-systems generate different sets
of formulas can be extremely difﬁcult. Indeed, even showing syntactically that two
Hilbert systems generate the same set of formulas can be highly non-trivial (recall
Exercise 1.6.5).

� � � and �

� �

��

Proving distinctness theorems was standard activity in the syntactic era; for in-
stance, Parry [359] showed that S2 and S3 are distinct, and papers addressing such
problems were common till the late 1950s. Algebraic methods were often used to
prove distinctness. The propositional symbols would be viewed as denoting the
elements of some algebra, and complex formulas interpreted using the algebraic
operations. Indeed, algebras were the key tool driving the technical development
of the period. For example, McKinsey [328] used them to analyze S2 and S4
and show their decidability; McKinsey and Tarski [330], McKinsey [329], and
McKinsey and Tarski [331] extended this work in a variety of directions (giving,
among other things, a topological interpretation of S4); while Dummett and Lem-
mon [125] built on this work to isolate and analyze S4.2 and S4.3, two important
normal logics between S4 and S5. But for all their technical utility, algebraic meth-
ods seemed of limited help in providing reliable intuitions about modal languages
and their associated logics. Sometimes algebraic elements were viewed as multiple
truth values. But Dugundji [124] showed that no logic between S1 and S5 could be
viewed as an �-valued logic for ﬁnite �, so the multi-valued perspective on modal
logic was not suited as a reliable source of insight.

40

1 Basic Concepts

The lack of a natural semantics brings up a deeper problem facing the syntac-
tic approach: how do we know we have considered all the relevant possibilities?
�) would
Nowadays the normal logic T (that is, K enriched with the axiom � �
be considered a fundamental logic of possibility; but Lewis overlooked T (it is in-
termediate between S2 and S4 and neither contains nor is contained by S3). More-
over, although Lewis did isolate two logics still considered important (namely S4
and S5), how could he claim that either system was, in any interesting sense, com-
plete? Perhaps there are important axioms missing from both systems? The exis-
tence of so many competing logics should make us skeptical of claims that it is easy
to ﬁnd all the relevant axioms and rules; and without precise, intuitively acceptable,
criteria of what the the reasonable logics are (in short, the type of criteria a decent
semantics provides us with) we have no reasonable basis for claiming success.

�

For further discussion of the work of this period, the reader should consult the
historical section of Bull and Segerberg [73]). We close our discussion of the syn-
tactic era by noting three lines of work that anticipate later developments: Carnap’s
state-description semantics, Prior’s work on temporal logic, and the J´onsson and
Tarski Representation Theorem for boolean algebras with operators.

A state description is simply a collection of propositional letters.

(Actually,
Carnap used state descriptions in his pioneering work on ﬁrst-order modal logic,
so a state for Carnap could be a set of ﬁrst-order formulas.) If � is a collection of
state descriptions, and � � �, then a propositional symbol � is satisﬁed at � if and
only � � �. Boolean operators are interpreted in the obvious way. Finally, �
� is
� satisﬁes �. (See,
satisﬁed at � � � if and only if there is some �
for example, Carnap [83, 84].)
Carnap’s interpretation of �

� in state descriptions is strikingly close to the idea
the use of an
of satisfaction in models. However one crucial idea is missing:
explicit relation � over state descriptions. In Carnap’s semantics, satisfaction for
� is deﬁned in terms of membership in � (in effect, � is taken to be � � �). This
implicit ﬁxing of � reduces the utility of his semantics: it yields a semantics for
one ﬁxed interpretation of �, but deprives us of the vital parameter needed to map
logical options.

� � such that �

�

Arthur Prior founded temporal logic (or as he called it, tense logic) in the early
1950s. He invented the basic temporal language and many other temporal lan-
guages, both modal and non-modal. Like most of his contemporaries, Prior viewed
the axiomatic exploration of concepts as one of the logician’s key tasks. But there
the similarity ends: his writings are packed with an extraordinary number of se-
mantic ideas and insights. By 1955 Prior had interpreted the basic modal lan-
guage in models based on �� � �� (see Prior [368], and Chapter 2 of Prior [369]),
and used what would now be called soundness arguments to distinguish logics.
Moreover, the relative expressivity of modal and classical languages (such as the
Prior-Meredith U-calculus [333]) is a constant theme of his writings; indeed, much

1.7 Historical Overview

41

of his work anticipates later work in correspondence theory and extended modal
logic. His work is hard to categorize, and impossible to summarize, but one thing
is clear: because of his inﬂuence temporal logic was an essentially semantically
driven enterprise. The best way into his work is via Prior [369].

With the work of J´onsson and Tarski [260, 261] we reach the most important
(and puzzling) might-have-beens in the history of modal logic. Brieﬂy, J´onsson
and Tarski investigated the representation theory of boolean algebras with operators
(that is, modal algebras). As we have remarked, while modal algebras were useful
tools, they seemed of little help in guiding logical intuitions. The representation
theory of J´onsson and Tarski should have swept this apparent shortcoming away for
good, for in essence they showed how to represent modal algebras as the structures
we now call models! In fact, they did a lot more than this. Their representation
technique is essentially a model building technique, hence their work gave the
technical tools needed to prove the completeness result that dominated the classical
era (indeed, their approach is an algebraic analog of the canonical model technique
that emerged 15 years later). Moreover, they provided all this for modal languages
of arbitrary similarity type, not simply the basic modal language.

Unfortunately, their work was overlooked for 20 years; not until the start of the
modern era was its signiﬁcance appreciated. It is unclear to us why this happened.
Certainly it didn’t help matters that J´onsson and Tarski do not mention modal logic
in their classic article; this is curious since Tarski had already published joint pa-
pers with McKinsey on algebraic approaches to modal logic. Maybe Tarski didn’t
see the connection at all: Copeland [94, page 13] writes that Tarski heard Kripke
speak about relational semantics at a 1962 talk in Finland, a talk in which Kripke
stressed the importance of the work by J´onsson and Tarski. According to Kripke,
following the talk Tarski approached him and said he was unable to see any con-
nection between the two lines of work.

Even if we admit that a connection which nows seems obvious may not have
been so at the time, a puzzle remains. Tarski was based in California, which in
the 1960s was the leading center of research in modal logic, yet in all those years,
the connection was never made. For example, in 1966 Lemmon (also based in
California) published a two part paper on algebraic approaches to modal logic [302]
which reinvented (some of) the ideas in J´onsson and Tarski (Lemmon attributes
these ideas to Dana Scott), but only cites the earlier Tarski and McKinsey papers.
We present the work by J´onsson and Tarski in Chapter 5; their Representation

Theorem underpins the work of the entire chapter.

The classical era (1959–1972)

‘Revolutionary’ is an overused word, but no other word adequately describes the
impact relational semantics (that is, the concepts of frames, models, satisfaction,

42

1 Basic Concepts

and validity presented in this chapter) had on the study of modal logic. Problems
which had previously been difﬁcult (for example, distinguishing Hilbert-systems)
suddenly yielded to straightforward semantic arguments. Moreover, like all revolu-
tions worthy of the name, the new world view came bearing an ambitious research
program. Much of this program revolved around the concept of completeness: at
last is was possible to give a precise and natural meaning to claims that a logic gen-
erated everything it ought to. (For example, K4 could now be claimed complete
in a genuinely interesting sense: it generated all the formulas valid on transitive
frames.) Such semantic characterizations are both simple and beautiful (especially
when viewed against the complexities of the preceding era) and the hunt for such
results was to dominate technical work for the next 15 years. The two outstanding
monographs of the classical era — the existing fragment of Lemmon and Scott’s
Intensional Logic [303], and Segerberg’s An Essay in Classical Modal Logic [396]
— are largely devoted to completeness issues.

Some controversy attaches to the birth of the classical era. Brieﬂy, relational
semantics is often called Kripke semantics, and Kripke [290] (in which S5-based
modal predicate logic is proved complete with respect to models with an implicit
global relation), Kripke [291] (which introduces an explicit accessibility relation �
and gives semantic characterization of some propositional modal logics in terms of
this relation) and Kripke [292] (in which relational semantics for ﬁrst-order modal
languages is deﬁned) were crucial in establishing the relational approach: they are
clear, precise, and ever alert to the possibilities inherent in the new framework: for
example, Kripke [292] discusses provability interpretations of propositional modal
languages. Nonetheless, Hintikka had already made use of relational semantics to
analyze the concept of belief and distinguish logics, and Hintikka’s ideas played
an important role in establishing the new paradigm in philosophical circles; see,
for example, [230]. Furthermore, it has since emerged that Kanger, in a series of
papers and monographs published in 1957, had introduced the basic idea of rela-
tional semantics for propositional and ﬁrst-order modal logic; see, for example,
Kanger [266, 267]. And a number of other authors (such as Arthur Prior, and
Richard Montague [341]) had either published or spoken about similiar ideas ear-
lier. Finally, the fact remains that J´onsson and Tarski had already presented and
generalized the mathematical ideas needed to analyze propositional modal logics
(though they do not discuss ﬁrst-order modal languages).

But disputes over priority should not distract the reader from the essential point:
somewhere around 1960 modal logic was reborn as a new ﬁeld, acquiring new
questions, methods, and perspectives. The magnitude of the shift, not who did
what when, is what is important here. (The reader interested in more detail on
who did what when, should consult Goldblatt [188]. Incidentally, after carefully
considering the evidence, Goldblatt concludes that Kripke’s contributions were the
most signiﬁcant.)

1.7 Historical Overview

43

So by the early 1960s it was was clear that relational semantics was an important
tool for classifying modal logics. But how could its potential be unlocked? The
key tool required — the canonical models we discuss in Chapter 4 — emerged
with surprising speed. They seem to have ﬁrst been used in Makinson [314] and
in Cresswell [97] (although Cresswell’s so-called subordination relation differs
slightly from the canonical relation), and in Lemmon and Scott [303] they appear
full-ﬂedged in the form that has become standard.

Lemmon and Scott [303] is a fragment of an ambitious monograph that was in-
tended to cover all then current branches of modal logic. At the time of Lemmon’s
death in 1966, however, only the historical introduction and the chapter on the ba-
sic modal languages had been completed. Nonetheless, it’s a gem. Although for
the next decade it circulated only in manuscript form (it was not published until
1977) it was enormously inﬂuential, setting much of the agenda for subsequent
developments. It unequivocally established the power of the canonical model tech-
nique, using it to prove general results of a sort not hitherto seen. It also introduced
ﬁltrations, an important technique for building ﬁnite models we will discuss in
Chapter 2, and used them to prove a number of decidability results.

While Lemmon and Scott showed how to exploit canonical models directly,
many important normal logics (notably, KL and the modal and temporal logic of
� ��, and their reﬂexive counter-
structures such as �
parts) cannot be analyzed in this way. However, as Segerberg [396, 395] showed,
it is possible to use canonical models indirectly: one can transform the canonical
model into the required form and prove these (and a great many other) complete-
ness results. Segerberg-style transformation proofs are discussed in Section 4.5.

� ��, and �

� ��, �

� ��, �

�

�

�

�

But although completeness and canonical models were the dominant issues of
the classical era, there is a small body of work which anticipates more recent
themes. For example, Robert Bull, swimming against the tide of fashion, used
algebraic arguments to prove a striking result: all normal extensions of S4.3 are
characterized by classes of ﬁnite models (see Bull [72]). Although model-theoretic
proofs of Bull’s Theorem were sought (see, for example, Segerberg [396, page
170]), not until Fine [136] did these efforts succeed. Kit Fine was shortly to play a
key role in the birth of the modern era, and the technical sophistication which was
to characterize his later work is already evident in this paper; we discuss Fine’s
proof in Theorem 4.96. As a second example, in his 1968 PhD thesis [263], Hans
Kamp proved one of the few (and certainly the most interesting) expressivity result
of the era. He deﬁned two natural binary modalities, since and until (discussed in
Chapter 7), showed that the standard temporal language was not strong enough to
deﬁne them, and proved that over Dedekind continuous strict total orders (such as

�

�

� ��) his new modalities offered full ﬁrst-order expressive power.
Summing up, the classical era supplied many of the fundamental concepts and
methods used in contemporary modal logic. Nonetheless, viewed from a modern

44

1 Basic Concepts

perspective, it is striking how differently these ideas were put to work then. For
a start, the classical era took over many of the goals of the syntactic era. Modal
investigations still revolved round much the same group of concepts: necessity,
belief, obligation and time. Moreover, although modal research in the classical era
was certainly not syntactical, it was, by and large, syntactically driven. That is —
with the notable exception of the temporal tradition — relational semantics seems
to have been largely viewed as a tool for analyzing logics: soundness results could
distinguish logics, and completeness results could give them nice characterizations.
Relational structures, in short, weren’t really there to be described — they were
there to fulﬁll an analytic role. (This goes a long way towards explaining the lack
of expressivity results for the basic modal language; Kamp’s result, signiﬁcantly,
was grounded in the Priorean tradition of temporal logic.) Moreover, it was a self-
contained world in a way that modern modal logic is not. Modal languages and
relational semantics:
the connection between them seemed clear, adequate, and
well understood. Surely nothing essential was missing from this paradise?

The modern era (1972–present)

Two forces gave rise to the modern era: the discovery of frame incompleteness re-
sults, and the adoption of modal languages in theoretical computer science. These
unleashed a wealth of activity which profoundly changed the course of modal logic
and continues to inﬂuence it till this day. The incompleteness results results forced
a fundamental reappraisal of what modal languages actually are, while the inﬂu-
ence of theoretical computer science radically changed expectations of what they
could be used for, and how they were to be applied.

Frame-based analyses of modal logic were revealing and intoxicatingly success-
ful — but was every normal logic complete with respect to some class of frames?
Lemmon and Scott knew that this was a difﬁcult question; they had shown, for
example that there were obstacles to adapting the canonical model method to ana-
lyze the logic yielded by McKinsey axiom. Nonetheless, they conjectured that the
answer was yes:

However, it seems reasonable to conjecture that, if a consistent normal K-
system S is closed with respect to substitution instances . . . then � determines
�. We have no proof of
a class �
this conjecture. But to prove it would be to make a considerable difference to
our theoretical understanding of the general situation. [303, page 76]

of world systems such that �

� iff ��

�

�

�

�

Other optimistic sentiments can be found in the literature of the period. Segerberg’s
thesis is more cautious, simply identifying it as ‘probably the outstanding question
in this area of modal logic at the present time’ [396, page 29].

The question was soon resolved — negatively. In 1972, S.K. Thomason [426]

1.7 Historical Overview

45

showed that there were incomplete normal logics in the basic temporal language,
and in 1974 Thomason [427] and Fine [137] both published examples of incom-
plete normal logics in the basic modal language. Moreover, in an important series
of papers Thomason showed that these results were ineradicable: as tools for talk-
ing about frames, modal languages were essentially monadic second-order logic in
disguise, and hence were intrinsically highly complex.

These results stimulated what remains some of the most interesting and innova-
tive work in the history of the subject. For a start, it was now clear that it no longer
sufﬁced to view modal logic as an isolated formal system; on the contrary, it was
evident that a full understanding of what modal languages were, required that their
position in the logical universe be located as accurately as possible. Over the next
few years, modal languages were to be extensively mapped from the perspective of
both universal algebra and classical model theory.

Thomason [426] had already adopted an algebraic perspective on the basic tem-
poral language. Moreover, this paper introduced general frames, showed that
they were equivalent to semantics based on boolean algebras with operators, and
showed that these semantics were complete in a way that the frame-based seman-
tics was not: every normal temporal logic was characterized by some algebra.
Goldblatt introduced the universal algebraic approach towards modal logic and
developed modal duality theory (the categorical study of the relation between rela-
tional structures endowed with topological structure on the one hand, and boolean
algebras with operators on the other). This led to a belated appreciation of the fun-
damental contributions made in J´onsson and Tarski’s pioneering work. Goldblatt
and Thomason showed that the concepts and results of universal algebra could be
applied to yield modally interesting results; the best known example of this is the
Goldblatt-Thomason theorem a model theoretic characterization of modally deﬁn-
able frame classes obtained by applying the Birkhoff variety theorem to boolean
algebras with operators. We discuss such work in Chapter 5 (and in Chapter 3 we
discuss the Goldblatt-Thomason theorem from the perspective of ﬁrst-order model
theory). Work by Blok made deeper use of algebras, and universal algebra became
a key tool in the exploration of completeness theory (we brieﬂy discuss Blok’s
contribution in the Notes to Chapter 5). The revival of algebraic semantics — to-
gether with a genuine appreciation of why it was so important — is one of the most
enduring legacies of this period.

But the modern period also ﬁrmly linked modal languages with classical model
theory. One line of inquiry that led naturally in this direction was the following:
given that modal logic was essentially second-order in nature, why was it so often
ﬁrst-order, and very simple ﬁrst-order at that? That is, from the modern perspec-
tive, incomplete normal logics were to be expected — it was the elegant results of
the classical period that now seemed in need of explanation. One type of answer
was given in the work of Sahlqvist [388], who isolated a large set of axioms which

46

1 Basic Concepts

guaranteed completeness with respect to ﬁrst-order deﬁnable classes of frames.
(We deﬁne the Sahlqvist fragment in Section 3.6, where we discuss the Sahlqvist
Correspondence Theorem, an expressivity result. The twin Sahlqvist Complete-
ness Theorem is proved algebraically in Theorem 5.91.) Another type of answer
was developed in Fine [140] and van Benthem [39, 40]; we discuss this work (albeit
from an algebraic perspective) in Chapter 5.

A different line of work also linked modal and classical languages: an investi-
gation of modal languages viewed purely as description languages. As we have
mentioned, the classical era largely ignored expressivity in favor of completeness.
The Sahlqvist Correspondence Theorem showed the narrowness of this perspec-
tive: here was a beautiful result about the basic modal language that did not even
mention normal modal logics! Expressivity issues were subsequently explored by
van Benthem, who developed the subject now known as correspondence theory;
see [41, 42]. His work has two main branches. One views modal languages as
tools for describing frames (that is, as second-order description languages) and
probes their expressive power. This line of investigation, together with Sahlqvist’s
pioneering work, forms the basis of Chapter 3. The second branch explores modal
languages as tools for talking about models, an intrinsically ﬁrst-order perspec-
tive. This lead van Benthem to isolate the concept of a bisimulation, and prove the
fundamental Characterization Theorem: viewed as a tool for talking about mod-
els, modal languages are the bisimulation invariant fragment of the corresponding
ﬁrst-order language. Bisimulation driven investigations of modal expressivity are
now standard, and much of the following chapter is devoted to such issues.

The impact of theoretical computer science was less dramatic than the discov-
ery of the incompleteness results, but its inﬂuence has been equally profound.
Burstall [80] already suggests using modal logic to reason about programs, but the
birth of this line of work really dates from Pratt [367] (the paper which gave rise
to PDL) and Pnueli [363] (which suggested using temporal logic to reason about
execution-traces of programs). Computer scientists tended to develop powerful
modal languages; PDL in its many variants is an obvious example (see Harel [215]
for a detailed survey). Moreover, since the appearance of Gabbay et al. [167], the
temporal languages used by computer scientists typically contain the until opera-
tor, and often additional operators which are evaluated with respect to paths (see
Clarke and Emerson [92]). Gabbay also noted the signiﬁcance of Rabin’s theo-
rem [372] for modal decidability (we discuss this in Chapter 6), and applied it to a
wide range of languages and logics; see Gabbay [155, 156, 154].

Computer scientists brought a new array of questions to the study of modal logic.
For a start, they initiated the study of the computational complexity of normal log-
ics. Already by 1977 Ladner [299] had showed that every normal logic between K
and S4 had a PSPACE-hard satisﬁability problem, while the results of Fischer and
Ladner [143] and Pratt [366] together show that PDL has an EXPTIME-complete

1.7 Historical Overview

47

satisﬁability problem. (These results are proved in Chapter 6.) Moreover, the in-
terest of the modal expressivity studies emerging in correspondence theory was
reinforced by several lines of work in computer science. To give one particularly
nice example, computer scientists studying concurrent systems independently iso-
lated the notion of bisimulation (see Park [358]). This paved the way for the work
of Hennessy and Milner [225] who showed that weak modal languages could be
used to classify various notions of process invariance.

But one of the most signiﬁcant endowments from computer science has actu-
ally been something quite simple: it has helped remove a lingering tendency to see
modal languages as intrinsically ‘intensional’ formalisms, suitable only for analyz-
ing such concepts as knowledge, obligation and belief. During the 1990s this point
was strongly emphasized when connections were discovered between modal logic
and knowledge representation formalisms. In particular, description logics are a
family of languages that come equipped with effective reasoning methods, and a
special focus on balancing expressive power and computational and algorithmic
complexity; see Donini et al. [123]. The discovery of this connection has lead to
a renewed focus on efﬁcient reasoning methods, dedicated languages that are ﬁne-
tuned for speciﬁc modeling tasks, and a variety of novel uses of modal languages;
see Schild [392] for the ﬁrst paper to make the connection between the two ﬁelds,
and De Giacomo [102] and Areces [12, 15] for work exploiting the connection.

And this is but one example. Links with computer science and other disciplines
have brought about an enormous richness and variety in modal languages. Com-
puter science has seen a shift of emphasis from isolated programs to complex enti-
ties collaborating in heterogeneous environments; this gives rise to new challenges
for the use of modal logic in theoretical computer science. For instance, agent-
based theories require ﬂexible modeling facilities together with efﬁcient reason-
ing mechanisms; see Wooldridge and Jennings [455] for a discussion of the agent
paradigm, and Bennet et al. [33] for the link with modal logic. More generally,
complex computational architectures call for a variety of combinations of modal
languages; see the proceedings of the Frontiers of Combining Systems workshop
series for references [16, 160, 273].

Similar developments took place in foundational research in economics. Game
theory (Osborne and Rubinstein [354]) also shows a nice interplay between the no-
tions of action and knowledge; recent years have witnessed an increasing tendency
to give a formal account of epistemic notions, cf. Battigalli and Bonanno [30] or
Kaneko and Nagashima [265]. For modal logics that combine dynamic and epis-
temic notions to model games we refer to Baltag [20] and van Ditmarsch [117].

Further examples abound. Database theory continues to be a fruitful source
of questions for logicians, modal or otherwise. For instance, developments in
temporal databases have given rise to new challenges for temporal logicians (see
Finger [142]), while decription logicians have found new applications for their

48

1 Basic Concepts

modeling and reasoning methods in the area of semistructured data (see Calvanese
et al. [82]).
In the related, but more philosophically oriented area of belief re-
vision, Fuhrmann [152] has given a modal formalization of one of the most in-
ﬂuential approaches in the area, the AGM approach [4]. Authors such as Fried-
man and Halpern [150], Gerbrandy and Groeneveld [177], De Rijke [112], and
Segerberg [403] have discussed various alternative modal formalizations.

Cognitive phenomena have long been of interest to modal logicians. This is clear
from examples such as belief revision, but perhaps even more so from language-
related work in modal logic. The feature logic mentioned in Example 1.17 is but
one example; authors such as Blackburn, Gardent, Meyer Viol, and Spaan [59, 53],
Kasper and Rounds [271, 386], Kurtonina [294], Kracht [287], and Reape [378]
have offered a variety of modal logical perspectives on grammar formalisms, while
others have analyzed the semantics of natural language by modal means; see Fer-
nando [134] for a sample of modern work along these lines.

During the 1980s and 1990s a number of new themes on the interface of modal
logic and mathematics received considerable attention. One of these themes con-
cerns links between modal logic and non-wellfounded set theory; work that we
should certainly mention here includes Aczel [2], Barwise and Moss [26], and Bal-
tag [19, 21]; see the Notes to Chapter 2 for further discussion. Non-wellfounded
sets and many other notions, such as automata and labeled transition systems,
have been brought together under the umbrella of co-algebras (cf. Jacobs and Rut-
ten [248]), which form a natural and elegant way to model state-based dynamic sys-
tems. Since it was discovered that modal logic is as closely related to co-algebras
as equational logic is to algebras, there has been a wealth of results reporting on
this connection; we only mention Jacobs [247], Kurz [297] and R¨oßiger [385] here.
Another 1990s theme on the interface of modal logic and mathematics concerns
an old one: geometry. Work by Balbiani et al. [18], Stebletsova [416] and Ven-
ema [441] indicates that modal logic may have interesting things to say about ge-
ometry, while Aiello and van Benthem [3] and Lemon and Pratt [304] investigate
the potential of modal logic as a tool for reasoning about space.

As should now be clear to all our readers, the simple question posed by the modal
satisfaction deﬁnition — what happens at accessible states? — gives us a natural
way of working with any relational structure. This has opened up a host of new
applications for modal logic. Moreover, once the relational perspective has been
fully assimilated, it opens up rich new approaches to traditional subjects: see van
Benthem [44] and Fagin, Halpern, Moses, and Vardi [133] for thoroughly modern
discussions of temporal logic and epistemic logic respectively.

1.8 Summary of Chapter 1
� Relational Structures: A relational structure is a set together with a collection

1.8 Summary of Chapter 1

49

of relations. Relational structures can be used to model key ideas from a wide
range of disciplines.

� Description Languages: Modal languages are simple languages for describing

relational structures.

� Similarity Types: The basic modal language contains a single primitive unary
operator �. Modal languages of arbitrary similarity type may contain many
modalities � of arbitrary arity.

� Basic Temporal Language: The basic temporal language has two operators �
and � whose intended interpretations are ‘at some time in the future’ and ‘at
some time in the past.’

� Propositional Dynamic Logic: The language of propositional dynamic logic
has an inﬁnite collection of modal operators indexed by programs � built up
from atomic programs using union �, composition �, and iteration �; additional
constructors such as intersection � and test � may also be used. The intended
interpretation of ���� is ‘some terminating execution of program � leads to a
state where � holds.’

� Arrow Logic: The language of arrow logic is designed to talk about any object
that may be represented by arrows; it has a modal constant �’ (‘skip’), a unary
operator � (‘converse’), and a dyadic operator � (‘composition’).

� Satisfaction: The satisfaction deﬁnition is used to interpret formulas inside mod-
els. This satisfaction deﬁnition has an obvious local ﬂavor: modalities are inter-
preted as scanning the states accessible from the current state.

� Validity: A formula is valid on a frame when it is globally true, no matter what
valuation is used. This concept allows modal languages to be viewed as lan-
guages for describing frames.

� General Frames: Modal languages can also be viewed as talking about general
frames. A general frame is a frame together with a set of admissible valuations.
General frames offer some of the advantages of both models and frames and are
an important technical tool.

� Semantic Consequence: Semantic consequence relations for modal languages
need to be relativized to classes of structures. The classical idea that the truth
of the premises should guarantee the truth of the conclusion can be interpreted
either locally or globally. In this book we almost exclusively use the local inter-
pretation.

� Normal Modal Logics: Normal modal logics are the unifying concept in modal
proof theory. Normal modal logics contain all tautologies, the K axiom and the
Dual axiom; in addition they should be closed under modus ponens, uniform
substitution and generalization.


