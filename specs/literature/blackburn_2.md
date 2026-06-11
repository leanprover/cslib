2

Models

In Section 1.3 we deﬁned what it means for a formula to be satisﬁed at a state in
a model — but as yet we know virtually nothing about this fundamental semantic
notion. What exactly can we say about models when we use modal languages
to describe them? Which properties of models can modal languages express, and
which lie beyond their reach?

In this chapter we examine such questions in detail. We introduce disjoint
unions, generated submodels, bounded morphisms, and ultraﬁlter extensions, the
‘big four’ operations on models that leave modal satisfaction unaffected. We dis-
cuss two ways to obtain ﬁnite models and show that modal languages have the ﬁnite
model property. Moreover, we deﬁne the standard translation of modal logic into
ﬁrst-order logic, thus opening the door to correspondence theory, the systematic
study of the relationship between modal and classical logic. All this material plays
a fundamental role in later work; indeed, the basic track sections in this chapter are
among the most important in the book.

But the central concept of the chapter is that of a bisimulation between two
models. Bisimulations reﬂect, in a particularly simple and direct way, the locality
of the modal satisfaction deﬁnition. We introduce them early on, and they gradually
come to dominate our discussion. By the end of the chapter we will have a good
understanding of modal expressivity over models, and the most interesting results
all hinge on bisimulations.

Chapter guide

Section 2.1: Invariance Results (Basic track). We introduce three classic ways of
constructing new models from old ones that do not affect modal satisfac-
tion: disjoint unions, generated submodels, and bounded morphisms. We
also meet isomorphisms and embeddings.

Section 2.2: Bisimulations (Basic track). We introduce bisimulations and show
that modal satisfaction is invariant under bisimulation. We will see that

50

2.1 Invariance Results

51

the model constructions introduced in the ﬁrst section are all special cases
of bisimulation, learn that modal equivalence does not always imply bisim-
ilarity, and examine an important special case in which it does.

Section 2.3: Finite Models (Basic track). Here we show that modal languages en-
joy the ﬁnite model property. We do so in two distinct ways: by the se-
lection method (ﬁnitely approximating a bisimulation), and by ﬁltration
(collapsing a model into a ﬁnite number of equivalence classes).
Section 2.4: The Standard Translation (Basic track). We start our study of cor-
respondence theory. By deﬁning the standard translation, we link modal
languages to ﬁrst-order (and other classical) languages and raise the two
central questions that dominate later sections: What part of ﬁrst-order logic
does modal logic correspond to? And which properties of models are de-
ﬁnable by modal means?

Section 2.5: Modal Saturation via Ultraﬁlter Extensions (Basic track). The ﬁrst
step towards obtaining some answers is to introduce ultraﬁlter extensions,
the last of the big four modal model constructions. We then show that al-
though modal equivalence does not imply bisimilarity, it does imply bisim-
ilarity somewhere else, namely in the ultraﬁlter extensions of the models
concerned.

Section 2.6: Characterization and Deﬁnability (Advanced track). We prove the
two main results of this chapter. First, we prove van Benthem’s theorem
stating that modal languages are the bisimulation invariant fragments of
ﬁrst-order languages. Second, we show that modally deﬁnable classes of
(pointed) models are those that are closed under bisimulations and ultra-
products and whose complements are closed under ultrapowers.
Section 2.7: Simulations and Safety (Advanced track). We prove two results that
give the reader a glimpse of recent work in modal model theory. The ﬁrst
describes the properties that are preserved under simulations (a one-way
version of bisimulation), the second characterizes the ﬁrst-order deﬁnable
operations on binary relations which respect bisimilarity.

2.1 Invariance Results

Mathematicians rarely study structures in isolation. They are usually interested in
the relations between different structures, and in operations that build new struc-
tures from old. Questions that naturally arise in such a context concern the struc-
tural properties that are invariant under or preserved by such relations and opera-
tions. We’ll not give precise deﬁnitions of these notions, but roughly speaking, a
property is preserved by a certain relation or operation if, whenever two structures
are linked by the relation or operation, then the second structure has the property

52

2 Models

if the ﬁrst one has it. We speak of invariance if the property is preserved in both
directions.

When it comes to this research topic, logic is no exception to the rule — indeed,
logicians add a descriptive twist to it. For instance, modal logicians want to know
when two structures, or perhaps two points in distinct structures, are indistinguish-
able by modal languages in the sense of satisfying the same modal formulas.

� be states in � and �

Deﬁnition 2.1 Let � and �
let � and �
the set of all � -formulas satisﬁed at �: that is, �� �

� be models of the same modal similarity type � , and
� respectively. The � -theory (or � -type) of � is
��. We say that � and
� are (modally) equivalent (notation: �
�) if they have the same � -theories.
The � -theory of the model � is the set of all � -formulas satisﬁed by all states
� are called (modally) equivalent

�

� �

�

�

�

�

�

in �: that is, �� �
(notation: �

�

�

��. Models � and �
�) if their theories are identical. �

�

We now introduce three important ways of constructing new models from old ones
which leave the theories associated with states unchanged: disjoint unions, gen-
erated submodels, and bounded morphisms. These constructions (together with
ultraﬁlter extensions, which we introduce in Section 2.5) play an important role
throughout the book. For example, in the following chapter we will see that they
lift to the level of frames (where they preserve validity), we will use them repeat-
edly in our work on completeness and complexity, and in Chapter 5 we will see
that they have important algebraic analogs.

Disjoint Unions
Suppose we have the following two models:

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

�

�

� �

�

Don’t worry that we haven’t speciﬁed the valuations — they’re irrelevant here. All
that matters is that � and � have disjoint domains, for we are now going to lump
them together to form the model �

�:

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

�

�

�

�

�

� �

�

� is called the disjoint union of � and �. It gathers together
The model �
all the information in the two smaller models unchanged: we have not altered the
way the points are related, nor the way atomic information is distributed. Suppose

�

�

2.1 Invariance Results

53

�

in �: is � still true at �

we’re working in the basic modal language, and suppose that a formula � is true at
�? More generally, is modal satisfaction
(say) �
preserved from points in the original models to the points in the disjoint union?
And what about the reverse direction: if a modal formula is true at some state in
�, is it also true at that same state in the smaller model it came from?

in �

�

�

�

�

The answer to these questions is clearly yes: modal satisfaction must be invariant
(that is, preserved in both directions) under the formation of disjoint unions. Modal
satisfaction is intrinsically local: only the points accessible from the current state
are relevant to truth or falsity. If we evaluate a formula � at (say) �, it is completely
irrelevant whether we perform the evaluation in � or �
�; � simply cannot
detect the presence or absence of states in other islands.

�

Deﬁnition 2.2 (Disjoint Unions) We ﬁrst deﬁne disjoint unions for the basic
modal language. We say that two models are disjoint if their domains contain
� (� � �), their
no common elements. For disjoint models �
disjoint union is the structure
� ��� �� � �, where � is the union of
, and for each proposition letter
the sets �
�, � ��� �

, � is the union of the relations �

���.

, �

, �

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

Now for the general case. For disjoint � -structures �

�

�

�

�

� ��

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

(� � �) of the same modal similarity type � , their disjoint union is the structure
� � ,

; for each �

� ��� �

� � �

�

such that � is the union of the sets �
; and � is deﬁned as in the basic modal case.

�

�

�

�

�

�

�

is the union

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

If we want to put together a collection of models that are not disjoint, we ﬁrst
have to make them disjoint (say by indexing the domains of these models). To use
the terminology introduced shortly, we simply take mutually disjoint isomorphic
copies of the models we wish to combine, and combine the copies instead. �

Proposition 2.3 Let � be a modal similarity type and, for all � � �, let �
be a
� -model. Then, for each modal formula �, for each � � �, and each element �
�. In words: modal satisfaction is
� iff
of �
invariant under disjoint unions.

, we have �

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

Proof. We will prove the result for the basic similarity type. The proof is by in-
duction on � (we explained this concept in Exercise 1.3.1). Let � be some index;
, that
we will prove, for each basic modal formula �, and each element � of �

�

�

�

� �

�

� iff �

� �

�

�, where � is the disjoint union

.

�

�

�

�

�

�

� �

� iff � � �

First suppose that � contains no connectives. Now, if � is a proposition letter
��� iff (by deﬁnition of � ) � � � ���
�, then we have �
iff �
�. On the other hand, � could be � (for the purposes of inductive
proofs it is convenient to regard � as a propositional letter rather than as a logical
connective). But trivially � is false at � in both models, so we have the desired
equivalence here too.

� �

�

�

�

�

54

2 Models

Our inductive hypothesis is that the desired equivalence holds for all formulas
containing at most � connectives (where � � �). We must now show that the
equivalence holds for all formulas � containing � � � connectives. Now, if � is of
the form �� or � � � this is easily done — we will leave this to the reader — so
as we are working with the basic similarity type, it only remains to establish the
�. Then
equivalence for formulas of the form �
�. By the inductive hypothesis,
there is a state � in �
�.

�. But by deﬁnition of �, we have ���, so �

�. So assume that �

�� and �

with �

� �

� �

�

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

For the other direction, assume that �

. Then
there is a � with ��� and �
�� for
some �, and by the disjointness of the universes we must have that � � �. But then
as well, so we may apply the inductive hypothesis;
we ﬁnd that � belongs to �
this yields �

� holds for some � in �
�. It follows by the deﬁnition of � that �

�, so we ﬁnd that �

�. �

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

�

�

�

We will use Proposition 2.3 all through the book — here is a simple application
which hints at the ideas we will explore in Chapter 7.

Example 2.4 Deﬁned modalities are a convenient shorthand for concepts we ﬁnd
useful. We have already seen some examples. In this book �, the ‘true at all ac-
��, and we have inductively deﬁned
cessible states modality’, is shorthand for �
a ‘true somewhere �-steps from here’ modality �
� for each natural number � (see
Example 1.22). But while it is usually easy to show that some modality is deﬁnable
(we need simply write down its deﬁnition), how do we show that some proposed
operator is not deﬁnable? Via invariance results! As an example, consider the
global modality. The global diamond E has as its (intended) accessibility relation
the relation � � � implicitly present in any model. That is:

�

� E� iff �

� �

�

� for some state � in �

�

�

� �

Its dual, A, the global box, thus has the following interpretation:

� A� iff �

� �

� for all states � in �

�

�

�

� �

Thus the global modality brings a genuinely global dimension to modal logic. But
is it deﬁnable in the basic modal language? Intuitively, no: as � and � work
locally, it seems unlikely that they can deﬁne a truly global modality over arbitrary
structures. Fine — but how do we prove this?

With the help of the previous proposition. Suppose we could deﬁne A. Then
we could write down an expression ���� containing only symbols from the basic
�. We
modal language such that for every model �, �
where
now derive a contradiction from this supposition. Consider a model �
where � holds nowhere. Let � be some
� holds everywhere, and a model �
����, so as (by assumption) ���� contains
point in �

. It follows that �

���� iff �

� �

� �

�

�

�

�

�

�

�

2.1 Invariance Results

55

�

�

�

�

�

� �

����. But this implies that �

only symbols from the basic modal language, by Proposition 2.3 we have that
� for every � in �
,
which, again by Proposition 2.3, in turn implies that �
�: contradiction. We
conclude that the global box (and hence the global diamond) is not deﬁnable in the
basic modal language.

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

So, if we want the global modality, then we either have to introduce it as a
primitive (we will do this in Section 7.1), or we have to work with restricted classes
of models on which it is deﬁnable (in Exercise 1.3.3 we worked with a class of
models in which we could deﬁne A in the basic temporal language). �

Generated submodels

Disjoint unions are a useful way of making bigger models from smaller ones — but
we also want methods for doing the reverse. That is, we would like to know when it
is safe to throw points away from a satisfying model without affecting satisﬁability.
Disjoint unions tell us a little about this (if a model is a disjoint union of smaller
models, we are free to work with the component models), but this is not useful in
practice. We need something sharper, namely generated submodels.

Suppose we are using the basic modal language to talk about a model � based
� ��, the integers with their usual order. It does not matter what the

on the frame �
valuation is — all that’s important is that � looks something like this:

�

. . .

�

��

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

�

. . .

�

�

�

�

�

�

�

�

�

First suppose that we form a submodel �
� of � by throwing away all the positive
numbers, and restricting the original valuation (whatever it was) to the remaining
numbers. So �

� looks something like this:

�

. . .

�

��

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

�

� (note that �

The basic modal language certainly can see that � and �
� are different. For
�) but is a dead
example, it sees that 0 has successors in � (note that �
�). So there’s no invariance result for arbitrary
end in �
� of � that is formed by omitting
submodels. But now consider the submodel �
the negative numbers, and restricting the original valuation to the numbers that
remain:

� � �

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

. . .

�

�

�

�

�

�

�

56

2 Models

Is � also
Suppose a basic modal formula � is satisﬁed at some point � in �.
�? The answer must be yes. The only points that
satisﬁed at the same point � in �
are relevant to �’s satisﬁability are the points greater than � — and all such points
belong to �
� satisﬁes a basic modal formula � at
�, then � must too.

�. Similarly, it is clear that if �

In short, it seems plausible that modal invariance holds for submodels which
are closed under the accessibility relation of the original model. Such models are
called generated submodels, and they do indeed give rise to the invariance result
we are looking for.

� ��� �� � � and �

Deﬁnition 2.5 (Generated Submodels) We ﬁrst deﬁne generated submodels for
� be two
the basic modal language. Let �
models; we say that �
� is the restriction of �
to �
� (that is:
� (that is: �
� is a generated submodel of �
for each �, �
(notation: �
� is a submodel of � and for all points � the following
closure condition holds:

�), and �
�). We say that �

� is the restriction of � to �

� is a submodel of � if �

�) if �

� � , �

��� � � ��� � �

� � � ��

� ��

� �

� �

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

if � is in �

�.
� and ���, then � is in �

For the general case, we say that a model �
submodel of the model �
is a submodel of � (with respect to �
condition is fulﬁlled for all �

� ��� �

� � �

� �

�

�

�

�

�

�

� ��

(notation: �

�

�

�

�

�

� �

� �

is a generated
�) whenever �
� � ), and the following closure

�

�

�

�

�

�

for all �

if � � �

� and �

��

� � � �

, then �

� � � � � �

� �

�.

�

�

�

�

�

Let � be a model, and � a subset of the domain of �; the submodel generated
by � is the smallest generated submodel of � whose domain contains � (such a
model always exists: why?). Finally, a rooted or point generated model is a model
that is generated by a singleton set, the element of which is called the root of the
frame. �

Proposition 2.6 Let � be a modal similarity type and let � and �
such that �
each element � of �
satisfaction is invariant under generated submodels.

� be � -models
� is a generated submodel of �. Then, for each modal formula � and
�. In words: modal

� we have that �

� iff �

� �

� �

�

�

�

Proof. By induction on �. The reader unused to such proofs should write out the
proof in full.
In Proposition 2.19 we provide an alternative proof based on the
observation that generated submodels induce a bisimulation. �

Four remarks. First, note that the invariance result for disjoint unions (Proposi-
tion 2.3) is a special case of the result for generated submodels: any component of

2.1 Invariance Results

57

a disjoint union is a generated submodel of the disjoint union. Second, using an
argument analogous to that used in Example 2.4 to show that the global box can’t
be deﬁned in the basic modal language, we can use Proposition 2.6 to show that we
cannot deﬁne a backward looking modality in terms of �; see Exercise 2.1.2. Thus
if we want such a modality we have to add it as a primitive — which is exactly what
we did, of course, when deﬁning the basic temporal language. Third, although we
have not explicitly discussed generated submodels for the basic temporal language,
PDL, or arrow logic, the required concepts are all special cases of Deﬁnition 2.5,
and thus the respective invariance results are special cases of Proposition 2.6. But
it is worth making a brief comment about the basic temporal language. When we
think explicitly in terms of bidirectional frames (see Example 1.25) it is obvious
. But when work-
that we are interested in submodels closed under both �
ing with the basic temporal language we usually leave �
implicit: we work with
. Thus a tem-
ordinary models ��� �� � �, and use �
poral generated submodel of ��� �� � � is a submodel ��
� that is closed
under both � and �
�. Finally, generated submodels are heavily used throughout
the book: given a model � that satisﬁes a formula � at a state �, very often the
ﬁrst thing we will do is form the submodel of � generated by �, thus trimming
what may be a very unwieldy satisfying model down to a more manageable one.

�, the converse of �, as �

and �

� �

� �

�

�

�

�

�

�

�

Morphisms for modalities

In mathematics the idea of morphisms or structure preserving maps is of funda-
mental importance. What notions of morphism are appropriate for modal logic?
That is, what kinds of morphism give rise to invariance results? We will approach
the answer bit by bit, introducing a number of important concepts on the way. We
will start by considering the general notion of homomorphism (this is too weak to
yield invariance, but it is the starting point for better attempts), then we will deﬁne
strong homomorphisms, embeddings, and isomorphisms (these do give us invari-
ance, but are not particularly modal), and ﬁnally we will zero in on the answer:
bounded morphisms.

Deﬁnition 2.7 (Homomorphisms) Let � be a modal similarity type and let � and
�)

� be � -models. By a homomorphism � from � to �

� (notation: � �

�

�

�

�

we mean a function � from � to �

� with the following properties.

(i) For each proposition letter � and each element � from �, if � � � ���,

then � ��� � �

�

���.

(ii) For each � � � and each �-ary �

��

, . . . , �
condition).

�

�

�

� � �

then �� ��

� � , and �� � ��-tuple � from �, if
(the homomorphic

�, . . . , � ��

�� � �

�

�

�

�

58

2 Models

We call � the source and �

� the target of the homomorphism.

�

Note that for the basic modal language, item (ii) is just this:

if ��� then �

�

� ���� ���.

Thus item (ii) simply says that homomorphisms preserve relational links.

Are modal formulas invariant under homomorphisms? No: although homomor-
phisms reﬂect the structure of the source in the structure of the target, they do
It is easy to turn this
not reﬂect the structure of the target back in the source.
observation into a counterexample, and we will leave this task to the reader as
Exercise 2.1.3.

So let us try and strengthen the deﬁnition. There is an obvious way of doing
so: turn the conditionals into equivalences. This leads to a number of important
concepts.

Deﬁnition 2.8 (Strong Homomorphisms, Embeddings and Isomorphisms) Let
� be � -models. By a strong homo-
� be a modal similarity type and let � and �
morphism of � into �
� which satisﬁes
the following stronger version of the above items (i) and (ii):

� we mean a homomorphism � �

�

�

�

(i) For each proposition letter � and element � from �, � � � ��� iff � ��� �

�

���.

�

(ii) For each � � � and each �-ary � in � and �� � ��-tuple � from �, ��

,
(the strong homomorphic

�

. . . , �
condition).

�

� � �

iff �� ��

�, . . . , � ��

�

�

�

�� � �

�

�

An embedding of � into �
� which is
injective. An isomorphism is a bijective strong homomorphism. We say that �
is isomorphic to �
�, if there is an isomorphism from � to

� is a strong homomorphism � �

�, in symbols �

�

�

�

�

�

�. �

�

�

Note that for the basic modal language, item (ii) is just:

��� iff �

�

� ���� ���.

That is, item (ii) says that relational links are preserved from the source model to
the target and back again. So it is not particularly surprising that we have a number
of invariance results.

Proposition 2.9 Let � be a modal similarity type and let � and �
Then the following holds:

� be � -models.

(i) For all elements � and �

� of � and �

surjective strong homomorphism � �
� are modally equivalent.
and �

�

�, respectively, if there exists a
�, then �

� with � ��� � �

�

�

2.1 Invariance Results

59

(ii) If �

�, then �

�

�

�

�.

�

�

Proof. The ﬁrst item follows by induction on �; the second one is an immediate
consequence. �

None of the above results is particularly modal. For a start, as in all branches of
mathematics, ‘isomorphic’ basically means ‘mathematically identical’. Thus, we
do not want to be able to distinguish isomorphic structures in modal (or indeed,
any other) logic. Quite the contrary: we want to be free to work with structures
‘up to isomorphism’ — as we did, for example, in our discussion of disjoint union,
when we talked of taking isomorphic copies. Item (ii) tells us that we can do this,
but it isn’t a surprising result.

But why is item (i), the invariance result for strong homomorphisms, not ‘gen-
uinely modal’? Quite simply, because there are many morphisms which do give
rise to invariance, but which fail to qualify as strong homomorphisms. To ensure
modal invariance we need to ensure that some target structure is reﬂected back in
the source, but strong morphisms do this in a much too heavy-handed way. The
crucial concept is more subtle.

Deﬁnition 2.10 (Bounded Morphisms — the Basic Case) We ﬁrst deﬁne bound-
� be models for the
ed morphisms for the basic modal language. Let � and �
� is a
basic modal language. A mapping � �
bounded morphism if it satisﬁes the following conditions:

� ��� �� � � �

� ��

� �

�

�

� �

�

�

�

�

(i) � and � ��� satisfy the same proposition letters.
(ii) � is a homomorphism with respect to the relation � (that is, if ��� then

�

� ���� ���).

�

(iii) If �

�

� ����

� then there exists � such that ��� and � ��� � �

� (the back

condition).

If there is a surjective bounded morphism from � to �
bounded morphic image of �, and write �
�. �

�

�

�, then we say that �

� is a

The idea embodied in the back condition is utterly fundamental to modal logic —
in fact, it is the idea that underlies the notion of bisimulation — so we need to get
a good grasp of what it involves right away. Here’s a useful example.

Example 2.11 Consider the models �
where

� �� , �, � � and �

�

�, �

�, �

�

�,

� ��

� � �

� (the natural numbers), ��� iff � � � � �, and � ��� � �� �

�

�

� is even�

�

� ��� ��, �

�

� ���� ��� ��� ���, and �

�

��� � ���.

� �

60

2 Models

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

. . .

�

�

�

�

�

�

�

. . .

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

Fig. 2.1. A bounded morphism

Now, let � � � � �

� be the following map:

�

if � is even
� if � is odd

� ��� �

�

Figure 2.1 sums this all up in a simple picture.

Now, � is not a strong homomorphism (why not?), but it is a (surjective) bounded
�. Let’s see why. Trivially � satisﬁes item (i) of the deﬁ-
morphism from � to �
nition. As for the homomorphic condition consider an arbitrary pair ��� � � �� in
�. There are two possibilities: � is either even or odd. Suppose � is even. Then
� � � is odd, so � ��� � � and � �� � �� � �. But then we have �
� ���� �� � ��,
as required. The argument for � odd is analogous.

�

� of � and assume that �
and � ��� � �
� is odd, � ��� � �, so by deﬁnition of �

And now for the interesting part: the back condition. Take an arbitrary element
�. We have to ﬁnd an � � � such that ���
�. Let’s assume that � is odd (the case for even � is similar). As
� �. But then
� since � � � is even, and by the deﬁnition of � we have that � � �

�, we must have that �

� �� � �� � �

� ����

�

�

is a successor of �. Hence, � � � is the � that we were looking for. �

Deﬁnition 2.12 (Bounded Morphisms — the General Case) The deﬁnition of
a bounded morphism for general modal languages is obtained from the above by
adapting the homomorphic and back conditions of Deﬁnition 2.10 as follows:

(ii)� For all �
(iii)� If �

�

� � , �

�

��

�

� � � �

implies �
then there exist �

�

� ����

�

�

� � � �

� ���� ��

� � � � � ��

�

�

�.

�

�

such that �

� � � �

��

� � � �

and

�

�

�

�

�

�

�

�

� ��

� � �

�

(for � � � � �). �

�

�

Example 2.13 Suppose we are working in the modal similarity type of arrow
logic; see Example 1.16 and 1.27. Recall that the language has a modal constant
�’, a unary operator � and a single dyadic operator �. Semantically, to these oper-
ators correspond a unary relation �, a binary � and a ternary �. We will deﬁne a

2.1 Invariance Results

61

bounded morphism from a square model to a model based on the addition of the
integer numbers. We will use the following notation: if � is an element of �
�,
then �

denotes its ﬁrst component, and �

its second component.

�

�

�

Consider the two models �

� ��� �� �� � � � � and �

�

�

�

�

�

�

� ��

� �

� �

� �

� �

�

where

� � �

�

�

and �

� �

�, � ��� iff �
, � � iff �

�

� �

, �

� �

and �

, ��� if �

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

, and ﬁnally, the valuation � is given by � ��� �

�

�

�

�

���

� �

� � �

� �

�

�

�

�

is even �,

� �

�

�

�, �
� is given by �

�

�

�

��� � �� �

�

� � is even �.

��� iff � � � � �, �

�

�� iff � � ��, �

�

� iff � � �, and the valuation

This example is best understood by looking at Figure 2.2. The left picture shows a
fragment of the model �; the points of �
� are represented as disks or circles,
depending on whether � is true or not. The diagonal is indicated by the dashed
diagonal line. The picture on the right-hand side shows the image under � of the
points in �

�.

�

�

. . .

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

��

�

��

�

�

. . .

�

�

�

�

�

�

�

�

�

��2
1

��

0

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

-1

�

��

-2

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

��

�

�

�

�

�

�

�

. . .

�

�

�

�

�

. . .

�

�

�

Fig. 2.2. Another bounded morphism.

We claim that the function � �

�

�

�

�

� given by

� �� � � �

� �

�

�

is a bounded morphism for this similarity type. The clause for the propositional
variables is trivial. For the unary relation � we only have to check that for any � in
� �. This is obviously true. We leave the case of the

iff �

�, �

� �

� �

�

�

�

�

�

�

binary relation � to the reader.

So let’s turn to the clauses for the ternary relation �. To check item (ii)� (the
homomorphic condition), assume that � ��� holds for �, � and � in � . That is,
we have that �

. But then we ﬁnd that

and �

, �

� �

� �

� �

�

�

�

�

�

�

� ��� � �

� �

� �

� �

� �

� �

� �

� �

� � �� � � � ����

�

�

�

�

�

�

�

�

62

2 Models

so by deﬁnition of �

� we do indeed ﬁnd that �
For item (iii)� (the back condition) assume that we have �

� ���� ���� �� �.

�

� �

�

�

� and �� � �

�. In other words, we have that �
� �� and � �� ��

the pairs � �� ��
ﬁnd that � ��� � � and � �� � � �
are the elements of � that we need to satisfy item (iii)�. �

� �� � ��

� �� �

� ��

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

� ����� for some
� � � �. Consider
�. It is obvious that � ���; we also
� � � � �. Hence � and �

� �

�

�

Deﬁnition 2.12 covers the basic temporal language, PDL, and arrow logic, as spe-
cial cases — but once more it is worth issuing a warning concerning the basic
is usually presented implicitly (as the converse
temporal language. Although �
of the relation � in some model ��� �� � �) we certainly cannot ignore it. Thus
a temporal bounded morphism from ��
� is a bounded
morphism from ��

� to ��
�.

� to ��

� �

� �

� �

� �

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

�

�

�

�

�

�

�

�

�

Proposition 2.14 Let � be a modal similarity type and let � and �
such that � �
� we have �
� iff �
under bounded morphisms.

� be � -models
�. Then, for each modal formula �, and each element � of
�. In words: modal satisfaction is invariant

� � ���

� �

�

�

�

�

�

�

Proof. Let �, �
� and � be as in the statement of the proposition. We will prove
that for each formula � and state �, �
�. The proof is
� iff �
by induction on �. We will assume that � is the basic similarity type, leaving the
general case to the reader.

� � ���

� �

�

�

�

The base step and the boolean cases are routine, so let’s turn to the case where
�. This means there is a state
�. By the

�. By the inductive hypothesis, �

�. Assume ﬁrst that �

� � ���

� �

�

�

�

�

� is of the form �
� with ��� and �
homomorphic condition, �

� �

�

�

� ���� ���, so �

�

� � ���

�

�.

�

For the other direction, assume that �

�. Thus there is a successor
�. Now we use the back condition
of � ��� in �
(of Deﬁnition 2.10). This yields a point � in � such that ��� and � ��� � �
�.
Applying the inductive hypothesis, we obtain �

�, such that �

�, so �

�, say �

�. �

� � ���

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

Here is a simple application: we will now show that any satisﬁable formula can be
satisﬁed in a tree-like model. To put it another way: modal logic has the tree model
property.

Let � be a modal similarity type containing only diamonds (thus if � is a
� -model, it has the form ��� �
is a binary rela-
tion on � ). In this context we will call a � -model � tree-like if the structure

� � � � � � �, where each �

� �

�

�

�

���

�

�

�

� � � is a tree in the sense of Example 1.5.

�

Proposition 2.15 Assume that � is a modal similarity type containing only dia-
� such
monds. Then, for any rooted � -model � there exists a tree-like � -model �
�. Hence any satisﬁable � -formula is satisﬁable in a tree-like model.
that �

�

�

2.1 Invariance Results

63

�

�

�

�

�

�

��� �

� � � � � �

, . . . , �

� � � there is a path ��

Proof. Let � be the root of �. Deﬁne the model �
consists of all ﬁnite sequences ��, �
operators ��
�, . . . , ��

� as follows. Its domain �
� such that � � � and for some modal
in �. Deﬁne
for � � �� � � � � �,
relates two sequences iff the second is an
and �
extension of the ﬁrst with a state from � that is a successor of the last element
of the ﬁrst sequence. Finally, �
iff �

� � ���. As the reader is asked to check in Exercise 2.1.4, the mapping
� to �,

deﬁnes a surjective bounded morphism from �

� is deﬁned by putting ��� �

� to hold if � � � � �, �

holds in �. That is, �

� � ��� �

� � � � � �

� � � � � �

� �� �

� � � ��

� � �

� � � � �

��� �

� �

���

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

�

�

�

�

�

�

�

thus �

� and � are equivalent.

But then it follows that any satisﬁable � -formula is satisﬁable in a tree-like
model. For suppose � is satisﬁable in some � -model at a point �. Let � be
the submodel generated by �. By Proposition 2.3, �
�, and as � is rooted
we can form an equivalent tree-like model �

� as just described. �

� �

�

� from � is well known in both modal logic
The method used to construct �
it is called unravelling (or unwinding, or unfolding).
In
and computer science:
� by treating the paths through � as ﬁrst class citizens: this
essence, we built �
untangles the (possibly very complex) way information is stored in �, and makes
it possible to present it as a tree. We will make use of unravelling several times in
later work; in the meantime, Exercise 2.1.7 asks the reader to extend the notion of
‘tree-likeness’ to arbitrary modal similarity types, and generalize Proposition 2.15.

Exercises for Section 2.1
2.1.1 Suppose we wanted an operator D with the following satisfaction deﬁnition: for any
�. This
model � and any formula �, �
operator is called the difference operator and we will discuss it further in Section 7.1. Is
the difference operator deﬁnable in the basic modal language?

� D� iff there is a � �� � such that �

� �

� �

�

2.1.2 Use generated submodels to show that the backward looking modality (that is, the �
of the basic temporal language) cannot be deﬁned in terms of the forward looking operator
�.

2.1.3 Give the simplest possible example which shows that the truth of modal formulas is
not invariant under homomorphisms, even if condition 1 is strengthened to an equivalence.
Is modal truth preserved under homomorphisms?

2.1.4 Show that the mapping � deﬁned in the proof of Proposition 2.15 is indeed a surjec-
tive bounded morphism.

2.1.5 Let �
of �s and �s, and ��� holds if � is a proper initial segment of � . Let �
frame of the natural numbers with the usual ordering.

� �� � �� be the transitive binary tree; that is, � is the set of ﬁnite strings
� �� be the

� �

�

64

2 Models

(a) Let �

� be the valuation on � given by �

�

�

��� � ��� � � �

� for each proposition
� to

� �

�

�

letter �. Deﬁne a valuation �

� on � and a bounded morphism from �

�

�

� �

(b) Let �

�

�.
� be the valuation on � given by �

letter �. Give a valuation �

�

�

�

� �

�.

� on � and a bounded morphism from �

��� � ��� � � � �� for each proposition
� to

� �

�

�

�

(c) Can you also ﬁnd surjective bounded morphisms?

2.1.6 Show that every model is the bounded morphic image of the disjoint union of point-
generated (that is: rooted) models. This exercise may look rather technical, but in fact it is
very straightforward — think about it!

2.1.7 This exercise generalizes Proposition 2.15 to arbitrary modal similarity types.

(a) Deﬁne a suitable notion of tree-like model that works for arbitrary modal similarity
� as being the parent node and of

types. (Hint: in case of �

, think of �

� � � �

�

�

�

�

�

�

�

� � � � � �

�

as the children.)

�

(b) Generalize Proposition 2.15 to arbitrary modal similarity types.

2.2 Bisimulations

What do the invariance results of the previous section have in common? They all
deal with special sorts of relations between two models, namely relations with the
following properties: related states carry identical atomic information, and when-
ever it is possible to make a transition in one model, it is possible to make a match-
ing transition in the other. For example, with generated submodels the inter-model
relation is identity, and every transition in one model is matched by an identical
transition in the other. With bounded morphisms, the inter-model relation is a func-
tion, and the notion of matching involves both the homomorphic link from source
to target, and the back condition which reﬂects target structure in the source.

This observation leads us to the central concept of the chapter: bisimulations.
Quite simply, a bisimulation is a relation between two models in which related
states have identical atomic information and matching transition possibilities. The
interesting part of the deﬁnition is the way it makes the notion of ‘matching transi-
tion possibilities’ precise.

Deﬁnition 2.16 (Bisimulations — the Basic Case) We ﬁrst give the deﬁnition
� be two
for the basic modal language. Let �
models.

� ��� �� � � and �

� ��

� �

� �

�

�

�

�

A non-empty binary relation � � � � �

� is called a bisimulation between �

and �

� (notation: � �

�

�

�

�) if the following conditions are satisﬁed.

(i) If �� �
(ii) If �� �

� then � and �
� and ���, then there exists �

� satisfy the same proposition letters.
� (in �

�) such that �� �

� and �

�

�

�

�

�

(the forth condition).

2.2 Bisimulations

65

(iii) The converse of (ii): if �� �

� and �

�

�

�

�

�, then there exists � (in �) such

that �� �

� and ��� (the back condition).

� are bisimilar, and we write � �

When � is a bisimulation linking two states � in � and �
and �
� such that � �
if there is some bisimulation between � and �

�, we sometimes write �

�, we write �

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

� in �

� we say that �
�. If there is a bisimulation
�; likewise,

� �

� �

�

�

�

�

�

�. �

Think of Deﬁnition 2.16 pictorially. Figure 2.3 shows the content of the forth
� and ��� (the solid arrow in � and the �-
clause. Suppose we know that �� �
link at the bottom of the diagram display this information). Then the forth condition
� that ‘completes the square’ (this is shown
says that it is always possible to ﬁnd a �
� and the dotted �-link at the top of the diagram). Note
by the dashed arrow in �
the symmetry between the back and forth clauses: to visualize the back clause,
simply reﬂect the picture through its vertical axis.

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

Fig. 2.3. The forth condition.

In effect, bisimulations are a relational generalization of bounded morphisms: we
drop the directionality from source to target (and with it the homomorphic con-
dition) and replace it with a back and forth system of matching moves between
models.

� shown in Figure 2.4 are bisimilar. To see
Example 2.17 The models � and �
this, deﬁne the following relation � between their states: � � ���� ��, ��� ��,
��� ��, ��� ��, ��� ��, ��� ���. Condition (i) of Deﬁnition 2.16 is obviously satisﬁed:
�-related states make the same propositional letters true. Moreover, the back-and-
forth conditions are satisﬁed too: any move in � can be matched by a similar move
in �

�, and conversely, as the reader should check.

This example also shows that bisimulation is a genuine generalization of the
� are bisimilar,

constructions discussed in the previous section. Although � and �
neither is a generated submodel nor a bounded morphic image of the other. �

66

2 Models

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

��

�

�

�

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

��

�

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

Fig. 2.4. Bisimilar models.

�

�

�

� ��� �

Deﬁnition 2.18 (Bisimulations — the General Case) Let � be a modal similarity
be � -models. A
type, and let �
� is called a bisimulation between � and
non-empty binary relation � � � � �
�) if the above condition (i) from Deﬁnition 2.16
is satisﬁed (that is, �-related states satisfy the same proposition letters) and in
addition the following conditions (ii)� and (iii)� are satisﬁed:

� (notation: � �

and �

� ��

� � �

� �

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

�

�

(ii)� If �� �

� and �

��

� � � �

then there are �

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

� � � �

�

�

�

and for all � (� � � � �) �

�

� �

�

�

(iii)� The converse of (ii)�: if �� �

� and �

�

�

�

�

�) such that

�

�

�

(in �

, . . . , �
(the forth condition).
then there are �

�

�

, . . . , �
(the back

�

(in � ) such that �
condition). �

�

��

� � � �

�

�

�

�

�

and for all � (� � � � �) �

�

� �

�

�

� � � �

Examples of bisimulations abound — indeed, as we have already mentioned, the
constructions of the previous section (disjoint unions, generated submodels, iso-
morphisms, and bounded morphisms), are all bisimulations:

Proposition 2.19 Let � be a modal similarity type, and let �, �
be � -models.

� and �

�

(� � �)

�

�

�

�

�, then �
(i) If �
(ii) For every � � � and every � in �
�, then �
(iii) If �
(iv) If � �

�, then �

�.

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

, �

� �

�

�

�

�

�

� �.

�

�.
� � for all � in �

�

�

� � ��� for all � in �.

�

�

�

�

�

and

by putting � � ���� �� � � �

Proof. We only prove the second item, leaving the others as Exercise 2.2.2. As-
sume we are working in the basic modal language. Deﬁne a relation � between
�. Then � is a bisimulation.
To see this, observe that clause (i) of Deﬁnition 2.16 is trivially fulﬁlled, and as to
is reproduced in
clauses (ii) and (iii), any �-step in �
, and by the disjoint-
that departs from a point that was originally
ness condition every �-step in
. The reader should extend this
in �
argument to arbitrary similarity types. �

, stems from a corresponding �-step in �

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

2.2 Bisimulations

67

We will now show that modal satisﬁability is invariant under bisimulations (and
hence, by Proposition 2.19, provide an alternative proof that modal satisﬁability is
invariant under disjoint unions, generated submodels, isomorphisms, and bounded
morphisms). The key thing to note about the following proof is how straight-
forward it is — the back and forth clauses in the deﬁnition of bisimulation are
precisely what is needed to push the induction through.

Theorem 2.20 Let � be a modal similarity type, and let �, �
for every � � � and �
formulas are invariant under bisimulation.

� implies that �

�, �

� �

�

�

�

�

� be � -models. Then,
�. In words, modal

�

Proof. By induction on �. The case where � is a proposition letter follows from
clause (i) of Deﬁnition 2.16, and the case where � is � is immediate. The boolean
cases are immediate from the induction hypothesis.

As for formulas of the form �

�, we have �

such that ��� and �
2.16 that there exists a �
hypothesis, �
clause (iii) of Deﬁnition 2.16.

� �

� �

�

�

�

�

� in �
�, hence �

�. As �

�

�

� such that �

�

�

� �

�

�

�

� �

� iff there exists a � in �
� we ﬁnd by clause (ii) of Deﬁnition
�. By the induction
�. For the converse direction use

� and �

�

�

�

�

�

�

�

The argument for the general modal case, with triangles �, is an easy extension

of that just given, as the reader should check. �

This ﬁnishes our discussion of the basics of bisimulation — so let’s now try and
understand the concept more deeply. Some of the remarks that follow are concep-
tual, and some are technical, but they all point to ideas that crop up throughout the
book.

Remark 2.21 (Bisimulation, Locality, and Computation) In the Preface we sug-
gested that the reader think of modal formulas as automata. Evaluating a modal
formula amounts to running an automaton: we place it at some state inside a struc-
ture and let it search for information. The automaton is only permitted to explore
by making transitions to neighboring states; that is, it works locally.

� in a different model �

Suppose such an automaton is standing at a state � in a model �, and we pick
�; would it notice the switch?
it up and place it at a state �
� are bisimilar, no. Our automaton cares only about the information
If � and �
at the current state and the information accessible by making a transition — it is
indifferent to everything else. Thus the deﬁnition of bisimulation spells out exactly
what we have to do if we want to fool such an automaton as to where it is being
evaluated. Viewed this way, it is clear that the concept of bisimulation is a direct
reﬂection of the locality of the modal satisfaction deﬁnition.

But there is a deeper link between bisimulation and computation than our infor-
mal talk of automaton might suggest. As we discussed in Example 1.3, labelled

68

2 Models

�

�

�

�

�

��

�

��

�

��

��

�

��

��

�

��

�

��

�

�

��

. . .

�

��

. . .

�

��

�

��

�

��

�

�� . . . . .

�

�

Fig. 2.5. Equivalent but not bisimilar.

transition systems (LTSs) are a standard way of thinking about computation: when
we traverse an LTS we build a sequence of state transitions — or to put it another
way, we compute. When are two LTSs computationally equivalent? More pre-
cisely, if we ignore practical issues (such as how long it takes to actually perform
a computation) when can two different LTSs be treated as freely exchangeable
(‘observationally equivalent’) black boxes? One natural answer is: when they are
bisimilar. Bisimulation turns out to be a very natural notion of equivalence for both
mathematical and computational investigations. For more on the history of bisim-
ulation and the connection with computer science, see the Notes. �

Remark 2.22 (Bisimulation and First-Order Logic) According to Theorem 2.20
modal formulas cannot distinguish between bisimilar states or between bisimilar
It follows
models, even though these states or models may be quite different.
that modal logic is very different from ﬁrst-order logic, for arbitrary ﬁrst-order
formulas are certainly not invariant under bisimulations. For example, the model

� of Example 2.17 satisﬁes the formula

�

��

�

�

��

�� �

� �

�� �

� �

�� �

� ���

� ���

� ��

�

� ��

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

if we assign the state � to the free variable �. This formula says that there is a
�, but
diamond-shaped conﬁguration of points, which is true of the point � in �
not of the state � in �. But as far as modal logic is concerned, �
� and �, being
bisimilar, are indistinguishable. In Section 2.4 we will start examining the links
between modal logic and ﬁrst-order logic more systematically. �

Now for a fundamental question: is the converse of Theorem 2.20 true? That is, if
two models are modally equivalent, must they be bisimilar? The answer is no.

Example 2.23 Consider the basic modal language. We may just as well work with
an empty set of proposition letters here. Deﬁne models � and � as in Figure 2.5,
where arrows denote �-transitions. Each of � and � has, for each � � �, a ﬁnite
branch of length �; the difference between the models is that, in addition, � has an
inﬁnite branch.

2.2 Bisimulations

69

One can show that for all modal formulas �, �

� (this is
easy if one is allowed to use some results that we will prove further on, namely
Propositions 2.31 and 2.33, but it is not particularly hard to prove from ﬁrst prin-
ciples, and the reader may like to try this). But even though � and �
� are modally
equivalent, there is no bisimulation linking them. To see this, suppose that there
was such a bisimulation �: we will derive a contradiction from this supposition.

� iff �

� �

� �

�

�

�

Since � and �

� are linked by �, there has to be a successor of �, say �

�

�

on the inﬁnite path from �

is linked to the ﬁrst point �
length of the (maximal) path leading from � through �
be the successive points on this path. Using the bisimulation conditions � � �
times, we ﬁnd points �
�, such
that �
does not; hence, there is no way that these two points can be bisimilar. �

on the inﬁnite path emanating from �

has a successor, but �

, . . . , �
and �

for each �. Now �

� � � �

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

, which
�. Suppose that � is the
, and let �, �

, . . . , �

�

Nonetheless, it is possible to prove a restricted converse to Theorem 2.20, namely
the Hennessy-Milner Theorem. Let � be a modal similarity type, and � a � -
model. � is image-ﬁnite if for each state � in � and each relation � in �, the
� is ﬁnite; observe that we are not putting any
set � ��
restrictions on the total number of different relations � in the model � — just that
each of them is image-ﬁnite.

� � ���

� � � � � �

� � � �

�

�

�

�

Theorem 2.24 (Hennessy-Milner Theorem) Let � be a modal similarity type,
� be two image-ﬁnite � -models. Then, for every � � � and
and let � and �
� iff �
�, �

�.

� �

�

�

�

�

�

�

Proof. Assume that our similarity type � only contains a single diamond (that is,
we will work in the basic modal language). The direction from left to right follows
from Theorem 2.20; for the other direction, we will prove that the relation � of
modal equivalence itself satisﬁes the conditions of Deﬁnition 2.16 — that is, we
show that the relation of modal equivalence on these models is itself a bisimulation.
(This is an important idea; we will return to it in Section 2.5.)

The ﬁrst condition is immediate. For the second one, assume that �

�

�

�

� with �

and ���. We will try to arrive at a contradiction by assuming that there is no �
� must
in �
be non-empty, for otherwise �
since �

�, which would contradict �

� is image-ﬁnite, �

�. Note that �

�. Let �

� and �

� ��

� �

� �

�

�

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

�. Furthermore, as �
�. By assumption, for every �

�

� must be ﬁnite, say
� there exists a formula �

�

�

�

� ��

� � � � � �

�

�

�

such that �

� �

but �

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

. It follows that

�

�

�

�

�

� �

��

� � � � � �

� and �

�

�

�

�

� �

��

� � � � � �

��

�

�

�

�

which contradicts our assumption that �

�. The third condition of Deﬁni-

�

�

� �

�
�
70

2 Models

tion 2.16 may be checked in a similar way. Extending the proof to other similarity
types is routine. �

Theorem 2.20 (together with the Hennessy-Milner Theorem) on the one hand, and
Example 2.23 on the other, mark important boundaries. Clearly, bisimulations have
something important to say about modal expressivity over models, but they don’t
tell us everything. Two pieces of the jigsaw puzzle are missing. For a start, we are
still considering modal languages in isolation: as yet, we have made no attempt to
systematically link them to ﬁrst-order logic. We will remedy this in Section 2.4 and
this will eventually lead us to a beautiful result, the Van Benthem Characterization
Theorem (Theorem 2.68): modal logic is the bisimulation invariant fragment of
ﬁrst-order logic.

The second missing piece is the notion of an ultraﬁlter extension. We will intro-
duce this concept in Section 2.5, and this will eventually lead us to Theorem 2.62.
Informally, this theorem says: modal equivalence implies bisimilarity-somewhere-
else. Where is this mysterious ‘somewhere else’? In the ultraﬁlter extension. As
we will see, although modally equivalent models need not be bisimilar, they must
have bisimilar ultraﬁlter extensions.

Remark 2.25 (Bisimulations for the Basic Temporal Language, PDL, and Ar-
row Logic) Although we have already said the most fundamental things that need
to be said on this topic (Deﬁnition 2.18 and Theorem 2.20 covers these languages),
a closer look reveals some interesting results for PDL and arrow logic. But let us
ﬁrst discuss the basic temporal language.

First we issue our (by now customary) warning. When working with the basic

temporal language, we usually work with models ��� �� � � and implicitly take �
to be �
�. Thus we need a notion of bisimulation which takes �
so we deﬁne a temporal bisimulation between models ��� �� � � and ��
to be a relation � between the states of the two models that satisﬁes the clauses
of Deﬁnition 2.16, and in addition the following two clauses (iv) and (v) requiring
that backward steps in one model should be matched by similar steps in the other
model:

� into account, and

� �

� �

�

�

�

�

�

(iv) If �� �
(v) The converse of (iv): if �� �

� and ���, then there exists �
� and �

�

� (in �

�) such that �� �

�.
�, then there exists � (in �) such

� and �

�

�

�

�

�

�

�

that �� �

� and ���.

If we don’t do this, we are in trouble. For example, if � is a model whose underly-
� is the submodel of � generated by �, then these
ing frame is the integers, and �
two models are bisimilar in the sense of Deﬁnition 2.16, and hence equivalent as
far as the basic modal language is concerned. But they are not equivalent as far as
the basic temporal language is concerned: �

� �, but �

� �.

� � �

� �

�

�

2.2 Bisimulations

71

Given our previous discussion, this is unsurprising. What is (pleasantly) sur-
prising is that things do not work this way in PDL. Suppose we are given two
regular models. Checking that these models are bisimilar for the language of PDL
means checking that bisimilarity holds for all the (inﬁnitely many) relations that
exist in regular models (see Deﬁnition 1.26). But as it turns out, most of this work
is unnecessary. Once we have checked that bisimilarity holds for all the relations
which interpret the basic programs, we don’t have to check anything else:
the
relations corresponding to complex programs will automatically be bisimilar. In
Section 2.7 we will introduce some special terminology to describe this: the oper-
ations in regular PDL’s modality building repertoire (�, ;, and �) will be called safe
for bisimulation. Note that taking the converse of a relation is not an operation that
is safe for bisimulation (in effect, that’s what we just noted when discussing the
basic temporal language); see Exercise 2.2.6.

What about arrow logic? The required notion of bisimulation is given by Def-
� we

inition 2.18; note that the clause for �’ reads that for bisimilar points � and �
have � � iff �

�. �

�

�

�

�

, and �
is a bisimulation linking �

Remark 2.26 (The Algebra of Bisimulations) Bisimulations give rise to alge-
is a bisimulation between �
braic structure quite naturally. For instance, if �
and �
a bisimulation between �
and �
, then the composition of �
and �
. It is also a rather easy observation
and �
that the set of bisimulations between two models is closed under taking arbitrary
(ﬁnite or inﬁnite) unions. This shows that if two points are bisimilar, there is al-
ways a maximal bisimulation linking them; see Exercise 2.2.8. Further information
on closure properties of the set of bisimulations between two models can be found
in Section 2.7. �

�

�

�

�

�

�

�

Exercises for Section 2.2
2.2.1 Consider a modal similarity type with two diamonds ��� and ���, and with � � ���.
Show that the following two models are bisimilar.

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

. . .

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

2.2.2 This exercise asks the reader to complete in detail the proof of Proposition 2.19,
which links bisimulations and the model constructions discussed in the previous section.
You should prove these results for arbitrary similarity types.

(a) Show that if �
(b) Show that if �

�

�, then �

�

�

�

�

�

�

is the disjoint union of the models �

(� � �), then, for each �,

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

(c) Show that if �
(d) Show that if �

� is a generated submodel of �, then �
� is a bounded morphic image of �, then �

�

�

�

�

�

�

72

2 Models

2.2.3 This exercise is about temporal bisimulations.

(a) Show from ﬁrst principles that the truth of basic temporal formulas is invariant
under temporal bisimulations. (That is, don’t appeal to any of the results proved in
this section.)

� be ﬁnite rooted models for basic temporal logic with � and � . Let
(b) Let � and �
� and �
� satisfy
the same basic temporal formulas with � and � , then there exists a basic temporal
bisimulation that relates � and �

�, respectively. Prove that if � and �

� be the roots of � and �

�.

2.2.4 Consider the binary until operator � . In a model �
reads:

� ��� �� � � its truth deﬁnition

�

�

� �

� ��� ��

iff

there is a � such that ��� and �
for all � such that ��� and ���: �

�

�, and

�

� �

Prove that � is not deﬁnable in the basic modal language. Hint: think about the following
two models, but with arrows added to make sure that the relations are transitive:

�

�

�

�

�

�

�

�

��

��

��

��

�

�

�

�

�

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

2.2.5 Consider the following two models, which we are going to use to interpret the basic
temporal language: � �
� makes � true at all
non-zero integers and �
� in addition makes � true at all points of the form ��� with � a
non-zero integer number.

�, where �

� and ��

� �� �

� �� �

� �

� �

�

�

�

�

�

�

(a) Prove that there is a temporal bisimulation between � � and ��, linking � (in the

one model) to � (in the other model).

(b) Let � be the progressive operator deﬁned by the following truth table:

�

�

� �

� �

iff

there are � and � such that � � � � � and

�

� �

�

� for all � between � and ��

Prove that this operator is not deﬁnable in the basic temporal language.

2.2.6 Suppose we have two bisimilar LTSs. Show that bisimilar states in these LTSs satisfy
exactly the same formulas of PDL.

2.2.7 Prove that two square arrow models �
ilar if and only if there is a relation � between pairs over � and pairs over �

� � � and �

� �

� �

�

�

�

�

�

�

� �

�

� are bisim-
� such that

�

(i) if ��� ��� ��
(ii) if ��� ��� ��
(iii) if ��� ��� ��
(iv) if ��� ��� ��

�

�

� �

� �

�

�

�

� �

�

� �

�

�

�, then ��� �� � � ��� iff ��
�, then � � � iff �
�, then �� � ��� ��
�,
�, then for any � � � there exists a �
�,

� and ��� ��� ��

���,

�,

� � �

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

�

��� ��� ��

� �

(v) and vice versa.

�

� �

� such that both

2.3 Finite Models

73

Must any two bisimilar square arrow models be isomorphic? (Hint: think of � ��� and
��� as the natural ordering relations of the rational and the real numbers, respectively.)

�

�

2.2.8 Suppose that ��

�

�. Prove that the relation �

�

� � � � � is a non-empty collection of bisimulations between � and
�. Conclude
is also a bisimulation between � and �
�;
.

� are bisimilar, then there is a maximal bisimulation between � and �

such that for any bisimulation � �

� we have � � �

�

�

�

�

�

�

�

�

that if � and �
that is, a bisimulation �

�

�

2.3 Finite Models
Preservation and invariance results can be viewed either positively or negatively.
Viewed negatively, they map the limits of modal expressivity:
they tell us, for
example, that modal languages are incapable of distinguishing a model from its
generated submodels. Viewed positively, they are a toolkit for transforming mod-
els into more desirable forms without affecting satisﬁability. Proposition 2.15 has
already given us a taste of this perspective (we showed that modal languages have
the tree model property) and it will play an important role when we discuss com-
pleteness in Chapter 4.

The results of this section are similarly double-edged. We are going to investi-
gate modal expressivity over ﬁnite models, and the basic result we will prove is that
modal languages have the ﬁnite model property: if a modal formula is satisﬁable
on an arbitrary model, then it is satisﬁable on a ﬁnite model.

Deﬁnition 2.27 (Finite Model Property) Let � be a modal similarity type, and
let � be a class of � -models. We say that � has the ﬁnite model property with
respect to � if the following holds: if � is a formula of similarity type � , and � is
satisﬁable in some model in �, then � is satisﬁable in a ﬁnite model in �. �

In this section we will mostly be concerned with the special case in which � in
Deﬁnition 2.27 is the collection of all � -models, so to simplify terminology we
will use the term ‘ﬁnite model property’ for this special case. The fact that modal
languages have the ﬁnite model property (in this sense) can be viewed as a lim-
itative result: modal languages simply lack the expressive strength to force the
existence of inﬁnite models. (By way of contrast, it is easy to write down ﬁrst-
order formulas which can only be satisﬁed on inﬁnite models.) On the other hand,
the result is a source of strength: we do not need to bother about (arbitrary) inﬁnite
models, for we can always ﬁnd an equivalent ﬁnite one. This opens the door to the
decidability results of Chapter 6. (The satisﬁability problem for ﬁrst-order logic,
as the reader probably knows, is undecidable over arbitrary models.)

We will discuss two methods for building ﬁnite models for satisﬁable modal
select a ﬁnite submodel of the satisfying
formulas. The ﬁrst is to (carefully!)
model, the second (called the ﬁltration method) is to deﬁne a suitable quotient
structure.

74

2 Models

Selecting a ﬁnite submodel

The selection method draws together four observations. Here is the ﬁrst. We know
that modal satisfaction is intrinsically local: modalities scan the states accessible
from the current state. How much of the model can a modal formula see from the
current state? That obviously depends on how deeply the modalities it contains are
nested.

Deﬁnition 2.28 (Degree) We deﬁne the degree of modal formulas as follows.

������ � �

������ � �

������� � ������

����� � �� � ����������� �������

����

��

� � � � � �

�� � � � ���������

�� � � � � �����

���

�

�

�

�

�

In particular, the degree of a basic modal formula �

� is � � ������. �

Second, we observe the following:

Proposition 2.29 Let � be a ﬁnite modal similarity type, and assume that our col-
lection of proposition letters is ﬁnite as well.

(i) For all �, up to logical equivalence there are only ﬁnitely many formulas of

degree at most �.

(ii) For all �, and every � -model � and state � of �, the set of all � -formulas
of degree at most � that are satisﬁed by �, is equivalent to a single formula.

Proof. We prove the ﬁrst item by induction on �. The case � � � is obvious. As
for the case �� �, observe that every formula of degree � �� � is a boolean combi-
�, where ������ � �. By
nation of proposition letters and formulas of the form �
the induction hypothesis there can only be ﬁnitely many non-equivalent such for-
mulas �. Thus there are only ﬁnitely many non-equivalent boolean combinations
�, where � has degree at most �. Hence,
of proposition letters and formulas �
there are only ﬁnitely many non-equivalent formulas of degree at most � � �.

Item (ii) is immediate from item (i). �

Third, we observe that there is a natural way of ﬁnitely approximating a bisimula-
tion. These ﬁnite approximations will prove crucial in our search for ﬁnite models.

Deﬁnition 2.30 (�-Bisimulations) Here we deﬁne �-bisimulations for modal
similarity types containing only diamonds, leaving the deﬁnition of the general
� be
case as part of Exercise 2.3.2. Let � and �
� are �-bisimilar (notation:
states of � and �

�, respectively. We say that � and �

� be models, and let � and �

2.3 Finite Models

75

�

�

�

�

�) if there exists a sequence of binary relations �

� � � � � �

with the

�

�

following properties (for � � � � �):

�

�

�

�

(i) ��
(ii) If ��
(iii) If ��
(iv) If ��

� then � and �

� agree on all proposition letters;

�

� and ���, then there exists �
� and �

� and ��
�, then there exists � with ��� and ��

� with �

�

�

�

�

�

�

�

�

�;
�. �

�

�

�

�

��

�

�

�

��

�

The intuition is that if �
if �
cise 2.3.1.

�, then �

�

�

�

�

�

�

�, then � and �

� bisimulate up to depth �. Clearly,
� for all � — but the converse need not hold; see Exer-

�

�

Fourth, we observe that for languages containing only ﬁnitely many proposition
letters, there is an exact match between modal equivalence and �-bisimilarity for
all �. That is, for such languages not only does �-bisimilarity for all � imply modal
equivalence, but the converse holds as well.

Proposition 2.31 Let � be a ﬁnite modal similarity type, � a ﬁnite set of proposi-
tion letters, and let � and �
� be models for this language. Then for every � in �
and �

�, the following are equivalent.

� in �

(i) �
(ii) � and �

�

�

�

�

� agree on all modal formulas of degree at most �.

It follows that ‘�-bisimilarity for all �’ and modal equivalence coincide as rela-
tions between states.

Proof. The implication (i) � (ii) may be proved by induction on �. For the con-
verse implication one can use an argument similar to the one used in the proof of
Theorem 2.24; we leave the proof as part of Exercise 2.3.2. �

It is time to draw these observations together. The following deﬁnition and lemma,
which are about rooted models, give us half of what we need to build ﬁnite models.

�

�

�

� ��� �

, . . . , �

Deﬁnition 2.32 Let � be a modal similarity type containing only diamonds. Let
, � � �� be a rooted � -model with root �. The notion of the
height of states in � is deﬁned by induction. The only element of height 0 is the
root of the model; the states of height � � � are those immediate successors of
elements of height � that have not yet been assigned a height smaller than � � �.
The height of a model � is the maximum � such that there is a state of height � in
�, if such a maximum exists; otherwise the height of � is inﬁnite.
For a natural number �, the restriction of � to � (notation: �

�) is deﬁned
as the submodel containing only states whose height is at most �. More precisely,
� �� � ��������� � ��,

�, where �

�� � ��

� � � � � �

� � � � � �

� �

�

�

�

�

�

� �

� ��

� �

�, and for each �, �

��� � � ��� � �

. �

��

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

76

2 Models

In words: the restriction of � to � contains all states that can be reached from
the root in at most � steps along the accessibility relations. Typically, this will not
give a generated submodel, so why does it interest us? Because, as we can now
show, given a formula � of degree � that is satisﬁable in some rooted model �, the
restriction of � to � contains all the states we need to satisfy �. To put it another
way: we are free to simply delete all states that lie beyond the ‘�-horizon.’

Lemma 2.33 Let � be a modal similarity type that contains only diamonds. Let
� be a rooted � -model, and let � be a natural number. Then, for every state � of

��, we have �

�

�

�

�

�

��� �

�

�

� �, where � � � � ���������.

�

Proof. Take the identity relation on �
��. We leave the reader to work out the
details as Exercise 2.3.3. The following comment may be helpful: in essence this
lemma tells us that if we are only interested in the satisﬁability of modal formulas
of degree at most �, then generating submodels of height � sufﬁces to maintain
satisﬁability. �

�

�

Putting together Proposition 2.31 and Lemma 2.33, we conclude that every satis-
ﬁable modal formula can be satisﬁed on a model of ﬁnite height. This is clearly
useful, but we are only halfway to our goal: the resulting model may still be inﬁ-
nite, as it may be inﬁnitely branching. We obtain the ﬁnite model we are looking
for by a further selection of points; in effect this discards unwanted branches and
leads to the desired ﬁnite model.

Theorem 2.34 (Finite Model Property — via Selection) Let � be a modal simi-
larity type containing only diamonds, and let � be a � -formula. If � is satisﬁable,
then it is satisﬁable on a ﬁnite model.

Proof. Fix a modal formula � with ������ � �. We restrict our modal simi-
larity type � and our collection of proposition letters to the modal operators and
proposition letters actually occurring in �. Let �
�.
such that
By Proposition 2.15, there exists a tree-like model �
,

be such that �
with root �

��. By Lemma 2.33 we have �

�. Let �

�� �

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

and by Proposition 2.31 it follows that �

� �

�

�.

�

�

�

�

�

�

�

�

� � � � � �

model �

By induction on � � � we deﬁne ﬁnite sets of states �
; the points in each �
�. Next, assume that �

with domain �

Deﬁne �

to be the singleton ��
been deﬁned. Fix an element � of �
many non-equivalent modal formulas whose degree is at most �, say �
For each such formula that is of the form ���� and holds in �
� from �
this selection process for every state in �
that have been selected in this way.

have already
. By Proposition 2.29 there are only ﬁnitely
.
at �, select a state
, and repeat
is deﬁned as the set of all points

�. Add all these �s to �
. �

such that �

�� and �

, . . . , �

and a (ﬁnal)

, . . . , �
will have height �.
, . . . , �

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

�

�

�

�

Finally, deﬁne �

as follows. Its domain is �

� � � �� �

; as each �

is ﬁnite, �

�

�

�

�

�

2.3 Finite Models

77

is ﬁnite. The relations and valuation are obtained by restricting the relations and
valuation of �

. By Exercise 2.3.4 we have that �

to the domain of �

� �

�

�

� �

, and hence �

� �

�

�, as required. �

�

�

�

�

�

�

�

�

�

How well does the selection method generalize to other modal languages? For
certain purposes it is ﬁne. For example, to deal with arbitrary modal similarity
types, the notion of a tree-like model needs to be adapted (in fact, we explained
how to do this in Exercise 2.1.7), but once this has been done we can prove a
general version of Proposition 2.15. Next, the notion of �-bisimilarity needs to
be adapted to other similarity types, but that too is straightforward (it is part of
Exercise 2.3.2). Finally, the selection process in the proof of Theorem 2.34 needs
adaptation, but this is unproblematic. In short, we can show that the ﬁnite model
property holds for arbitrary similarity types using the selection method.

The method has a drawback: the input model for our construction may satisfy
important relational properties (such as being symmetric), but the end result is al-
ways a ﬁnite tree-like model, and the desired relational properties may be (and
often are) lost. So if we want to establish the ﬁnite model property with respect
to a class of models satisfying additional properties — something that is very im-
portant in practice — we may have to do additional work once we have obtained
our ﬁnite tree-like model. In such cases, the selection method tends to be harder
to use than the ﬁltration method (which we discuss next). Nonetheless, the idea of
(intelligently!) selecting points to build submodels is important, and (as we will
see in Section 6.6 when we discuss NP-completeness) the idea really comes into
its own when the model we start with is already ﬁnite.

Finite models via ﬁltrations

We now examine the classic modal method for building ﬁnite models: ﬁltration.
Whereas the selection method builds ﬁnite models by deleting superﬂuous material
from large, possibly inﬁnite models, the ﬁltration method produces ﬁnite models
by taking a large, possibly inﬁnite model and identifying as many states as possible.
We ﬁrst present the ﬁltration method for the basic modal language.

Deﬁnition 2.35 A set of formulas � is closed under subformulas (or: subformula
closed) if for all formulas �, �
�; if �� � � then
. (For the basic modal
so is �; and if �
language, this means that if �

� � �, then so is �.) �

� � then so are � and �

� � � then so are �

�: if � � �

, . . . , �

� � � � � �

��

�

�

�

�

�

Deﬁnition 2.36 (Filtrations) We work in the basic modal language. Let �
��� �� � � be a model and � a subformula closed set of formulas. Let �

be the

�

�

78

2 Models

�

�

�

�

�

�

�

�

. . .�

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

���

���

�

�

�

�

�

Fig. 2.6. A model and its ﬁltration

��

relation on the states of � deﬁned by:

�

�

�

� iff for all � in �: �

�

� �

�

� iff �

� �

��.

�

�

Note that �
is an equivalence relation. We denote the equivalence class of a
state � of � with respect to �
, or simply by ��� if no confusion will
arise. The mapping � �� ��� that sends a state to its equivalence class is called the
natural map.
Let �

� � � � �. Suppose �

is any model ��

by ���

� such

� ����

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

that:

�

�

� �

.

(i) �
(ii) If ��� then �
(iii) If �
(iv) �

�

�

�

����� �.

����� � then for all �

��� � ���� �

�

� �

�

� � �, if �
��, for all proposition letters � in �.

� then �

� �

� �

�

�

�

�.

Then �

�

is called a ﬁltration of � through �. �

�

Because of item (ii), the natural map associated with any ﬁltration is guaranteed to
be a homomorphism (see Deﬁnition 2.7). And at ﬁrst glance it may seem that it
is even guaranteed to be a bounded morphism (see Deﬁnition 2.10), for item (iii)
seems reminiscent of the back condition. Unfortunately, this is not the case, as the
following example shows.

Example 2.37 Let � be the model �
���� � � �� � � � ��, and � has � ��� �

�

Further, assume that � � �

�

� �� � �, where � � ���� ��, ��� ��, ��� ����

� ��� and � ��� � ���.

�

�� ��. Clearly � is subformula closed. Then,
��� � �����, is a
�, where �

�

�

the model �
ﬁltration of � through �. See Figure 2.6.

� ������ ����� ������ ����� ����� ������ �

Clearly, � can not be a bounded morphic image of �: any bounded morphism
would have to preserve the formula �, and the natural map does not preserve �, and
need not, because � is not an element of our subformula closed set �. �

2.3 Finite Models

79

But in many other respects ﬁltrations are well-behaved. For a start, the method
gives us a bound (albeit an exponential one) on the size of the resulting ﬁnite model:

Proposition 2.38 Let � be a ﬁnite subformula closed set of basic modal formulas.
� is a ﬁltration of � through a subformula closed set �,
For any model �, if �
then �

� nodes (where ������ � denotes the size of �).

� contains at most �

�����

�

Proof. The states of �
with domain �
It follows from the deﬁnition of �

�

. Let � be the function
��.
that � is well deﬁned and injective. Thus

� �

�

�

�

and range � �� � deﬁned by ������ � �� � � �

� are the equivalence classes in �

������

� � ������ �� �� � �

�

�

�����

�

�. �

Moreover — crucially — ﬁltrations preserve satisfaction in the following sense.

Theorem 2.39 (Filtration Theorem) Consider the basic modal language. Let
�� be a ﬁltration of � through a subformula closed set �.
� iff

Then for all formulas � � �, and all nodes � in �, we have �

�� ��

� �

� �

�

� �

�

�

�

�

�

�

�

� ���

�

�.

Proof. By induction on �. The base case is immediate from the deﬁnition of �
� .
The boolean cases are straightforward; the fact that � is closed under subformulas
allows us to apply the inductive hypothesis.

So suppose �

� � � and �

� �

�

�. As �

� is a ﬁltration, �
thus by the inductive hypothesis �

� �

�

�

�

�. Then there is a � such that ��� and
����� �. As � is subformula closed, � � �,

�

�

Conversely, suppose �
� such that �

�.
�. Thus there is a state �� � in
�. As � � �, by the inductive hypothesis
�. So the third clause in Deﬁnition 2.36 is applicable, and we conclude

� � � and �

����� � and �

�. Hence �

� ���

� ���

� �� �

� �� �

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

that �

� �

�

�

�. �

Observe that clauses (ii) and (iii) of Deﬁnition 2.36 are designed to make the modal
case of the induction step go through in the proof above.

But we still have not done one vital thing: we have not actually shown that ﬁl-
trations exist! Observe that the clauses (ii) and (iii) in Deﬁnition 2.36 only impose
� — but we have not yet shown that a suitable
conditions on candidate relations �
� can always be found. In fact, there are always at least two ways to deﬁne binary

�

relations that fulﬁll the required conditions. Deﬁne �

� and �

� as follows:

(i) �
(ii) �

�

�

����� � iff ��
����� � iff for all formulas �

� �����

�

�

� �� � ��

�.

�

�

� in �: �

� �

�

� implies �

� �

�

�

�.

These relations — which are not necessarily distinct — give rise to the smallest
and largest ﬁltrations respectively.

80

2 Models

Lemma 2.40 Consider the basic modal language. Let � be any model, � any
the set of equivalence classes induced
subformula closed set of formulas, �
by �
� and
� is

� are ﬁltrations of � through �. Furthermore, if ��

� the standard valuation on �

. Then both ��

, and �

��

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

�

�

�

�

any ﬁltration of � through � then �

�

�

� �

� �

�.

�

�

�

� �

� �

Proof. We show that ��
It sufﬁces to show that �

� is a ﬁltration; the rest is left as an exercise.
� fulﬁlls clauses (ii) and (iii) of Deﬁnition 2.36. But
� satisﬁes clause (ii) by deﬁnition, so it remains to check clause (iii). Suppose
����� �, there exist
����� �, and further suppose that �
� � � and �
�, then because
� �� � such that ��
� ��� and �
� � �, thus as

�. As � � � and �

�. But ��

�. But �

�. As �

�, so �

�

�

�

�

�

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

�, we get �
� it follows that �

�. �

�

�

� �

Theorem 2.41 (Finite Model Property — via Filtrations) Let � be a basic mo-
dal formula. If � is satisﬁable, then it is satisﬁable on a ﬁnite model. Indeed, it is
� nodes, where � is the number
satisﬁable on a ﬁnite model containing at most �
of subformulas of �.

Proof. Assume that � is satisﬁable on a model �; take any ﬁltration of � through
the set of subformulas of �. That � is satisﬁed in the ﬁltration is immediate from
Theorem 2.39. The bound on the size of the ﬁltration is immediate from Proposi-
tion 2.38. �

There are several points worth making about ﬁltrations. The ﬁrst has to do with
the possible loss of properties when moving from a model to one of its ﬁltrations.
As we have already discussed, a drawback of the selection method is that it can be
hard to preserve such properties. Filtrations are far better in this respect — but they
certainly are not perfect. Let us consider the matter more closely.

�

�

�

� �

� �

Suppose ��

� is a ﬁltration of ��� �� � �. Now, clause (ii) of Deﬁ-
� is a homomorphism with
nition 2.36 means that the natural map from � to �
respect to the accessibility relation �. Thus any property of relations which is pre-
served under such maps will automatically be inherited by any ﬁltration. Obvious
examples include reﬂexivity and right unboundedness ����� ����.

However, many interesting relational properties are not preserved under homo-
morphisms: transitivity and symmetry are obvious counterexamples. Thus we need
to ﬁnd special ﬁltrations which preserve these properties. Sometimes this is easy;
for example, the smallest ﬁltration preserves symmetry. Sometimes we need new
ideas to ﬁnd a good ﬁltration; the classic example involves transitivity. Let’s see
what this involves.

Lemma 2.42 Let � be a model, � a subformula closed set of formulas, and �

�

2.3 Finite Models

81

�

�

�

�

�

�

� . . .

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

Fig. 2.7. Filtrating a model based on �

�

� ��

the set of equivalence classes induced on � by �
on �

deﬁned by:

�

. Let �

� be the binary relation

�

�

����� � iff for all �, if �

� � � and �

�

� �

� �

�

� then �

�

� �

�

�

�.

If � is transitive then ��

�

�

�

� �

� �

� is a ﬁltration and �

� is transitive.

Proof. Left as Exercise 2.3.5. �

In short, ﬁltrations are ﬂexible — but it is not a matter of ‘plug and play’. Creativity
is often required to exploit them.

The second point worth making is that ﬁltrations of an inﬁnite model through a
ﬁnite set manage to represent an inﬁnite amount of information in a ﬁnitary manner.
It seems obvious, at least from an intuitive point of view, that this can only be
achieved by identifying lots of points. As we have seen in Example 2.37, an inﬁnite
chain may be collapsed onto a single reﬂexive point by a ﬁltration. An even more
informative example is provided by models based on the rationals. For instance,
� �� � �; then
what happens to the density condition in the ﬁltration? Let �
any (ﬁnite) ﬁltration of � has the form displayed in Figure 2.7. What is going
on here? Instead of viewing models as structures made up of states and relations
between them, in the case of ﬁltrations it can be useful to view them as sets of
states (namely, the sets of identiﬁed states) and relations between those sets. The
following deﬁnition captures this idea.

� �

�

Deﬁnition 2.43 Let ��� �� � � be a transitive frame. A cluster on ��� �� � � is
a subset � of � that is a maximal equivalence relation under �. That is, the
restriction of � to � is an equivalence relation, and this is not the case for any
other subset � of � such that � � �.

A cluster is simple if it consists of a single reﬂexive point, and proper if it con-

tains more than one point. �

As Figure 2.7 shows, a (ﬁnite) ﬁltration of �
� �� can be thought of as resulting in
a ﬁnite linear sequence of clusters, perhaps interspersed with singleton irreﬂexive
points (no two of which can be adjacent). The reader is asked to check this claim
in Exercise 2.3.9. Clusters will play an important role in Section 4.5.

�

To conclude this section we brieﬂy indicate how the ﬁltration method can be
extended to other modal languages. Let us ﬁrst consider modal languages based

82

2 Models

on arbitrary modal similarity types � . Fix a � -model �
subformula closed set � as in Deﬁnition 2.36. Suppose �
is a � -model where �

� are as in Deﬁnition 2.36, and for �

� �� , �

and �

� ��

�

�

�

, � �
, �
� � , �

�

�

�

, �

�

�

�

�

�

and a

�

�

�

�

�

�

satisfy

�

�.
, . . . , �
, then �

�

(ii)� If �
(iii)� If �

��

� � � �

�

then �

�

�����

�

�

�

� � � � ��

�

�����

� � � � ��

�

�

�, then for all �

� �, if �

��

� � � � � �

� � �

�

�

�

and �

� �

, . . . , �

� �

�

�

�

�

� �

��

� � � � � �

�.

� �

�

�

�

�

�

�

Then �

�

is a � -ﬁltration of � through �.

�

With this deﬁnition at hand, Proposition 2.38 and Theorem 2.39 can be reformu-
lated and proved for � -ﬁltrations, and suitable versions of the smallest and largest
ﬁltrations can also be deﬁned, resulting in a general modal analog of Theorem 2.41,
the Finite Model Property.

What about basic temporal logic, PDL, and arrow logic? It turns out that the
ﬁltration method works well for all of these. For basic temporal logic we need to
issue the customary warning (we need to be explicit about what the ﬁltration does
�), but with this observed, matters are straightforward. Exercise 2.3.7 asks the
to �
reader to deﬁne transitive ﬁltrations for the basic temporal language.

Matters are far more interesting (and difﬁcult) with PDL — but here too, by
making use of a clever idea called the Fisher-Ladner closure, it is possible to use a
ﬁltration style argument to show that PDL has the ﬁnite model property; we will do
this in Section 4.8 as part of a completeness proof (Theorem 4.91). Exercise 2.3.10
deals with the ﬁnite model property for arrow logic.

Exercises for Section 2.3
2.3.1 Find two models � and �
for all �, but it is not the case that �
a pair of models in the previous section.)

�

� and states � and �

� in these models such that �

�

�

�

�

� are bisimilar. (Hint: we drew a picture of such

�

2.3.2 Generalize the deﬁnition of �-bisimulations (Deﬁnition 2.30) from diamond-only
to arbitrary modal languages. Then prove Proposition 2.31 (that � bisimilarity for all �
implies modal equivalence and conversely) for arbitrary modal languages.

2.3.3 Lemma 2.33 tells us that if we are only interested in the satisﬁability of modal for-
mulas of degree at most �, we can delete all states that lie beyond the �-horizon without
affecting satisﬁability. Prove this.

2.3.4 The proof of Theorem 2.34 uses a selection of points argument to establish the ﬁnite
model property. But no proof details were given for the last (crucial) claim in the proof,
namely that ��

� is �-bisimilar to ��

�. Fill in this gap.

� �

� �

2.3.5 First show that not every ﬁltration of a transitive model is transitive. Then prove
Lemma 2.42. That is, show that the relation �
� deﬁned there is indeed a ﬁltration, and that
any ﬁltration of a transitive model that makes use of �

� is guaranteed to be transitive.

2.4 The Standard Translation

83

2.3.6 Finish the proof of Lemma 2.40. That is, prove that the ﬁltrations �
� are
indeed the smallest and the largest ﬁltration, respectively. In addition, give an example of
a model and a set of formulas for which �

� coincide.

� and �

� and �

2.3.7 Show that every transitive model ��� �� � � has a transitive temporal ﬁltration. (Take
care to specify what the ﬁltration does to �
�.)

2.3.8 Call a frame or model euclidean if it satisﬁes ���� ����� � ��� � � ��� �, and let
� be the class of euclidean models. Fix a formula �, and let � be the smallest subformula
closed set of formulas containing � that satisﬁes, for all formulas �: if �
� � �, then
�.) Note that in general, � will be

� � �. (Recall that � is an abbreviation of �

��

�

inﬁnite.

�

�

(a) Prove that �
(b) Prove that every euclidean model can be ﬁltrated through � to a euclidean model.
(c) Show that every euclidean model satisﬁes the following modal reduction principles:
��. That is, prove that

�� and ���

��, ���

��, ���

�.

���

� �

��

�

�

�

�

the formulas ���
Conclude that � is ﬁnite modulo equivalence on euclidean models.

�, . . . are true throughout every euclidean model.

� �

��

(d) Prove that the basic modal similarity type has the ﬁnite model property with respect
to the class of euclidean models. Can you prove this result simply by ﬁltrating
through any subformula closed set of formulas containing �?

2.3.9 Show that any ﬁnite ﬁltration of a model based on the rationals with their usual or-
dering is a ﬁnite linear sequence of clusters, perhaps interspersed with singleton irreﬂexive
points, no two of which can be adjacent.

2.3.10 Consider the similarity type �

� of arrow logic.

(i) Show that �
models.

� has the ﬁnite model property with respect to the class of all arrow

(ii) Consider the class of arrow models based on arrow frames �

� ��� �� �� � � such
that for all �, � and � in � we have (i) � ��� iff � ��� iff � ��� and (ii) � ��� and
� � iff � � �. Prove that arrow formulas have the ﬁnite model property with respect
to this class of arrow models.

(iii) Prove that �

� does not have the ﬁnite model property with respect to the class of all
square models. (Hint: try to express that the extension of the propositional variable
� is a dense, linear ordering.)

2.4 The Standard Translation
In the Preface we warned the reader against viewing modal logic as an isolated
formal system (remember Slogan 3?), yet here we are, halfway through Chapter 2,
and we still haven’t linked modal logic with the wider logical world. We now put
this right. We deﬁne a link called the standard translation. This paves the way
for the results on modal expressivity in the sections that follow, for the study of
frames in the following chapter, and for the introduction of the guarded fragment
in Section 7.4.

We ﬁrst specify our correspondence languages — that is, the languages we will

translate modal formulas into.

84

2 Models

�

�

Deﬁnition 2.44 For � a modal similarity type and � a collection of proposition
��� be the ﬁrst-order language (with equality) which has unary pred-
letters, let �
icates �
, . . . in
, �
, �
�, and an �� � ��-ary relation symbol �
for each (�-ary) modal operator � in
our similarity type. We write ���� to denote a ﬁrst-order formula � with one free
variable, �. �

, . . . corresponding to the proposition letters �

, �

, �

�

�

�

�

�

�

�

We are now ready to deﬁne the standard translation.

Deﬁnition 2.45 (Standard Translation) Let � be a ﬁrst-order variable. The stan-
dard translation ��
��� is
deﬁned as follows:

taking modal formulas to ﬁrst-order formulas in �

�

�

�

��

�

��� � � �

��

�

��� � � �� �

��

��

���� � �

���

�

�

��

��

��

�� � �� �

��� �

���

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

� � � � � �

�� � ��

� � � ��

��

��

� � � �

�

��

��

�

�

��

� � � � � �

� ��

���

�

�

�

�

, . . . , �

where �
are fresh variables (that is, variables that have not been used so far
in the translation). When working with the basic modal language, the last clause
boils down to:

�

��

��

�

�� � �� ���� �

�����

�

�

�

�, and we
Note that (to keep notation simple) we prefer to use � rather than �
will continue to do this. We leave to the reader the task of working out what
�� is, but we will point out that for the basic modal language

� � � � � �

��

��

�

�

�

�

�

the required clause is:

��

��

�

�� � �� ���� �

����� �

�

�

�

Example 2.46 Let’s see how this works. Consider the formula �

��

��

�

�

� � ��� � ��

����

�

�

�

�

�

�

�

� � ���

�

�

�

� � ��.

�

�

� ��

����

� �

�

�

��

��

�

�

�

�� �

�

�����

�

�

� ��

����

� ���

���

�

�

��

�

�

���� � ��

��

�

�

�

�

�

�

� ��

����

� ���

���

�

� � �

� � ��

��

�

�

�

�

�

�

�

Note that (this version of) the standard translation leaves the choice of fresh vari-
ables unspeciﬁed. For example, ��

� � �

� ���

����

� �

���

�

�� is a legitimate translation of �

� � ��, and indeed there are inﬁnitely

�

�

��

���

���

���

��

���

��

��

2.4 The Standard Translation

85

many others, all differing only in the bound variables they contain. Later in the
section we remove this indeterminacy — elegantly. �

�

It should be clear that the standard translation makes good sense: it is essentially
a ﬁrst-order reformulation of the modal satisfaction deﬁnition. For any modal for-
mula �, ��
��� will contain exactly one free variable (namely �); the role of this
free variable is to mark the current state; this use of a free variable makes it pos-
sible for the global notion of ﬁrst-order satisfaction to mimic the local notion of
modal satisfaction. Furthermore, observe that modalities are translated as bounded
quantiﬁers, and in particular, quantiﬁers bounded to act only on related states; this
is the obvious way of mimicking the local action of the modalities in ﬁrst-order
logic. Because of its importance it is worth pinning down just why the standard
translation works.

�

�

�

�

�

Models for modal languages based on a modal similarity type � and a collection
of proposition letters � can also be viewed as models for �
���. For example,
if � contains just a single diamond �, then the corresponding ﬁrst-order language
��� has a binary relation symbol � and a unary predicate symbol corresponding
to each proposition letter in � — and a ﬁrst-order model for this language needs to
provide an interpretation for these symbols. But a (modal) model �
supplies precisely what is required: the binary relation � can be used to interpret
� can be used to interpret the unary predicate
the relation symbol �, and the set � ��
. This should not come as a surprise. As we emphasized in Chapter 1 (especially
Sections 1.1 and 1.3) there is no mathematical distinction between modal and ﬁrst-
order models — both modal and ﬁrst-order models are simply relational structures.
������, which means
Thus it makes perfect sense to write things like �
��� is satisﬁed (in the usual sense of ﬁrst-order
that the ﬁrst-order formula ��
logic) in the model � when � is assigned to the free variable �.

� ��� �� � �

��

��

�

�

�

�

�

Proposition 2.47 (Local and Global Correspondence on Models) Fix a modal
similarity type � , and let � be a � -formula. Then:

(i) For all � and all states � of �: �
(ii) For all �: �

� iff �

�� ��

��

�

���.

� iff �

� �

�

������.

�� ��

�

Proof. By induction on �. We leave this to the reader as Exercise 2.4.1. �

�

Summing up: when interpreted on models, modal formulas are equivalent to ﬁrst-
order formulas in one free variable. Fine — but what does that give us? Lots!
Proposition 2.47 is a bridge between modal and ﬁrst-order logic — and we can use
this bridge to import results, ideas, and proof techniques from one to the other.

if � is a set of
Example 2.48 First-order logic has the compactness property:
ﬁrst-order formulas, and every every ﬁnite subset of � is satisﬁable, then so is �

86

2 Models

itself. It also has the downward L¨owenheim-Skolem property: if a set of ﬁrst-order
formulas has an inﬁnite model, then it has a countably inﬁnite model.

It follows that modal logic must have both these properties (over models) too.
Consider compactness. Suppose � is a set of modal formulas every ﬁnite subset
of which is satisﬁable — is � itself satisﬁable? Yes. Consider the set ���
� � � �. As every ﬁnite subset of � has a model it follows (reading item (i) of
��� � � � � � does
Proposition 2.47 left to right) that every ﬁnite subset of �
too, and hence (by ﬁrst-order compactness) that this whole set is satisﬁable in some
model, say �. But then it follows (this time reading item (i) of Proposition 2.47
right to left) that � is satisﬁable in �, hence modal satisﬁability over models is
compact.

��� �

��

�

�

And there’s interesting trafﬁc from modal logic to ﬁrst-order logic too. For ex-
ample, a signiﬁcant difference between modal and ﬁrst-order logic is that modal
logic is decidable (over arbitrary models) but ﬁrst-order logic is not. By using our
understanding of modal decidability, it is possible to locate novel decidable frag-
ments of ﬁrst-order logic, a theme we will return to in Section 7.4 when we discuss
the guarded fragment. �

Just as importantly, the standard translation gives us a new research agenda for
investigating modal expressivity: correspondence theory. The central aim of this
chapter is to explore the expressivity of modal logic over models — but how is ex-
pressivity to be measured? Proposition 2.47 suggests an interesting strategy: try to
characterize the fragment of ﬁrst-order logic picked out by the standard translation.
It is obvious on purely syntactic grounds that the standard translation is not
surjective (standard translations of modal formulas contain only bounded quan-
tiﬁers) — but could every ﬁrst-order formula (in the appropriate correspondence
language) be equivalent to the translation of a modal formula? No. This is very
easy to see: whereas modal formulas are invariant under bisimulations, ﬁrst-order
formulas need not be; thus any ﬁrst-order formula which is not invariant under
bisimulations cannot be equivalent to the translation of a modal formula. We have
seen such a formula in Section 2.2, (namely ��

�� �

�� �

� �

� �

��

��

�

�

�

� ���

� ���

� ��

�

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

�), and it is easy to ﬁnd simpler examples.

Thus the (ﬁrst-order formulas equivalent to) standard translations of model for-
mulas are a proper subset of the correspondence language. Which subset? Here’s
a nice observation. The standard translation can be reformulated so that it maps
���, namely a certain ﬁnite-
every modal formula into a very small fragment of �
variable fragment. Suppose the variables of �
��� have been ordered in some way.
Then the �-variable fragment of �
��� formulas that contain
only the ﬁrst � variables. As we will now see, by judicious reuse of variables, a
modal language with operators of arity at most � can be translated into the � � �-
���. (Reuse of variables is the name of the game when
variable fragment of �

��� is the set of �

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

2.4 The Standard Translation

87

working with ﬁnite variable fragments. For example, we can express the existence
of three different points in a linear ordering using only two variables as follows:
��� �� � � � �� �� � ���.)

Proposition 2.49

(i) Let � be a modal similarity type that only contains di-
amonds. Then, every � -formula � is equivalent to a ﬁrst-order formula
containing at most two variables.

(ii) More generally, if � does not contain modal operators � whose arity ex-
ceeds �, all � -formulas are equivalent to ﬁrst-order formulas containing at
most � � � variables.

Proof. Assume � contains only diamonds ���, ���, . . . ; proving the general case
is left as Exercise 2.4.2. Fix two distinct individual variables � and �. Deﬁne two
of the standard translation as follows.
variants ��

and ��

�

�

�

�

��

��� = � �
��� = � �� �
���� = �
�� � �� = ��
������ = �� ��

��

�

�

�

�

��

��� = � �
��� = � �� �
���� = �
�� � �� = ��
������ = �� ��

��

�

�

��

�

��

��

��

��

��

�

���

�

���

�

�

�

�

�

�

�� �

����

��

��

�� �

��

����.

��� �

��� �

��

��

���

�

�

��

�

���

-translation contains at most the two variables

�

Then, for any � -formula �, its ��
� and �, and ��

��� is equivalent to the original standard translation of �. �

�

Example 2.50 Let’s see how this modiﬁed standard translation works. Consider
again the formula �

� � ��.

�

�

��

��

�

�

� � ��� � �� ���� �

�

� � ���

�

�

�

�

�

� �� ���� � ��� ���� �

���� � ����

��

�

� �� ���� � ��� ���� � � �� � ����

That is, we just keep ﬂipping between the two variables � and �. The result is
a translation containing only two variables (instead of the three used in Exam-
ple 2.46). As a side effect, the indeterminacy associated with the original version
of the standard translation has disappeared. �

This raises another question:
is every ﬁrst-order formula ���� in two variables
equivalent to the translation of a basic modal formula? Again the answer is no.
There is even a ﬁrst-order formula in a single variable � which is not equivalent
to any modal formula, namely ���. To see this, assume for the sake of a con-
tradiction that � is a modal formula such that ��
��� is equivalent to ���. Let
� be a singleton reﬂexive model and let � be the unique state in �; obviously
�� ������. Let � be a model based on the strict
(irrespective of the valuation) �
ordering of the integers; obviously (again, irrespective of the valuation), for every

�

88

2 Models

�� ������ �. Let � be the relation which links every integer with the
integer �, �
unique state in �, and assume that the valuations in � and � are such that � is
a bisimulation (for example, make all proposition letters true at all points in both
models). As �
� (after all,
�� ������, it follows by Proposition 2.47 that �
���). But for any integer �, we have that
by assumption ��� is equivalent to ��
�. Hence (again by Proposition 2.47 and our assumption
�� ����� �, contradicting the

��� is equivalent to ���) we have that �

�, hence �

� �

�

� �

�

�

�

�

that ��
fact that �

�

�� ������ �.

We will not discuss correspondence theory any further here, but in Section 2.6
we will prove one of its central results, the Van Benthem Characterization Theo-
rem: a ﬁrst-order formula is equivalent to the translation of a modal formula if and
only if it is invariant under bisimulations.

Proposition 2.47 is also going to help us investigate modal expressivity in other

ways, notably via the concept of deﬁnability.

Deﬁnition 2.51 Let � be a modal similarity type, � a class of � -models, and � a
set of formulas over � . We say that � deﬁnes or characterizes a class � of models
within � if for all models � in � we have that � is in � iff �
� . If � is
the class of all � -models, we simply say that � deﬁnes or characterizes �; we omit
brackets whenever � is a singleton. We will say that a formula � deﬁnes a property
whenever � deﬁnes the class of models satisfying that property. �

�

It is immediate from Proposition 2.47 that if a class of models is deﬁnable by a set
of modal formulas, then it is also deﬁnable by a set a ﬁrst-order formulas — but
this is too obvious to be interesting. The important way in which Proposition 2.47
helps, is by making it possible to exploit standard model construction techniques
from ﬁrst-order model theory. For example, in Section 2.6 we will prove Theo-
rem 2.75 which says that a class of (pointed) models is modally deﬁnable if and
only if it is closed under bisimulations and ultraproducts (an important construc-
tion known from ﬁrst-order model theory; see Appendix A), and its complement
is closed under ultrapowers (another standard model theoretic construction).
It
would be difﬁcult to overemphasize the importance of the standard translation; it
is remarkable that such a simple idea can lead to so much.

To conclude this section, let’s see how to adapt these ideas to the basic temporal
language, PDL, and arrow logic. The case of basic temporal logic is easy: all we
have to do is add a clause for translating the backward looking operator � :

��

�

��

�

�� � �� ���� �

�����

�

�

Note that we are using the more sophisticated approach introduced in the proof
. (Thus we
of Proposition 2.49: ﬂipping between two translations ��
really need to add a mirror clause which ﬂips the variables back.) So, just like

and ��

�

�

2.4 The Standard Translation

89

the basic modal language, the basic temporal language can be mapped into a two
variable fragment of the correspondence language. Moreover (again, as with the
basic modal language) not every ﬁrst-order formula in two variables is equivalent
to (the translation of) a basic temporal formula (see Exercise 2.4.3).

Propositional dynamic logic calls for more drastic changes. Let’s ﬁrst look at the
�-free fragment — that is, at PDL formulas without occurrences of the Kleene star.
In PDL both formulas and modalities are recursively structured, so we’re going to
need two interacting translation functions: one to handle the formulas, the other to
handle the modalities. The only interesting clause in the formula translation is the
following:

��

��

��

������ � �� �

��� �

�����

�

��

�

��

calls on ��

That is, instead of returning a ﬁxed relation symbol (say �), the formula translation
to start recursively decomposing the program �. Why does this
part of the translation require two free variables? Because its task is to deﬁne a
binary relation.

��

�

��

��

�

��� � �

�� (and similarly for other pairs of variables)

��

��

��

��

� �

� �

��

� �

��

�

��

��

��

�

�

�

�

��

��

��

��

� �

� � �� �

��

� �

��

���

��

��

��

�

�

�

�

It follows that we can translate the �-free fragment of PDL into a three variable
fragment of the correspondence language. The details are worth checking; see
Exercise 2.4.4.

But the really drastic change comes when we consider the full language of PDL
(that is, with Kleene star). Recall that a program �
� is interpreted using the reﬂex-
. But the reﬂexive, transitive closure of an arbitrary
ive, transitive closure of �
relations is not a ﬁrst-order deﬁnable relation (see Exercise 2.4.5). So the standard
translation for PDL needs to take us to a richer background logic than ﬁrst-order
logic, one that can express this concept. Which one should we use? There are
many options here, but to motivate our actual choice recall the deﬁnition of the
meaning of a PDL program �

�:

�

where �

�

is deﬁned by

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

�� iff � � � and �

�

�

��

�� iff �� ��

�

�� � �����

Thus, if we were allowed to write inﬁnitely long disjunctions, it would be easy to
capture the meaning of an iterated program �

�:

�

�� iff �� � �� � �

��

�

�� �

��

� � � �

��

��

� � � � � �

�

���

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

90

2 Models

In inﬁnitary logic we can do this. More precisely, in �
we are allowed to form
formulas as in ﬁrst-order logic, and, in addition, to build countably inﬁnite dis-
as the target logic for the standard
junctions and conjunctions. We will take �
translation of PDL. We have seen most of the clauses we need: we use the clauses
for the �-free fragment given above, and in addition the following clause to cater
for the Kleene star:

�

�

�

�

�

�

��

��

��

� �

�

�� � �� �

��� �

��

� � � �

�

�

��� � � � � �

�

�����

��

��

��

��

�

��

�

�

�

�

�

�

�

This example of PDL makes an important point vividly: we cannot always hope
to embed modal logic into ﬁrst-order logic. Indeed in the following chapter we
will see that when it comes to analyzing the expressive power of modal logic at
the level of frames, the natural correspondence language (even for the basic modal
language) is second-order logic.

There is nothing particularly interesting concerning the standard translation for
the arrow language of Example 1.16. However, this changes when we turn to
square models: in Exercise 2.4.6 the reader is asked to prove that on this class of
models, the arrow language corresponds to a ﬁrst-order language with binary pred-
icate symbols, and that, in fact, it is expressively equivalent to the three variable
fragment of such a language.

Exercises for Section 2.4
2.4.1 Prove Proposition 2.47. That is, check that the standard translation really is correct.

2.4.2 Prove Proposition 2.49 for arbitrary modal languages. That is, show that if � does
not contain modal operators � whose arity exceeds �, all � -formulas are equivalent to
ﬁrst-order formulas containing at most � � � variables.

2.4.3 Show that there are ﬁrst-order formulas ���� using at most two variables that are not
equivalent to the standard translation of a basic temporal formula.

2.4.4 In this exercise you should ﬁll in some of the details for the standard translation for
PDL.

(a) Check that the translation for the �-free fragment of PDL really does map all such
formulas into the three variable fragment of the corresponding ﬁrst-order language.
(b) Show that in fact, there is a translation into the two variable fragment of this corre-

sponding ﬁrst-order language.

2.4.5 The aim of this exercise is to show that taking the reﬂexive, transitive closure of a
binary relation is not a ﬁrst-order deﬁnable operation.

(a) Show that the class of connected graphs is not ﬁrst-order deﬁnable:

2.5 Modal Saturation via Ultraﬁlter Extensions

91

(i) For � �

�, let �

�

be the graph given by a cycle of length � � �:

�

�

� ���� � � � � ��� ���� � � ��� �� � �� �� � � � � � �� � ���� ��� ��� ����

Show that for every � �
order sentences of quantiﬁer rank at most � as the disjoint union �
(ii) Conclude that the class of connected graphs is not ﬁrst-order deﬁnable.

� the graph �

� and � � �

satisﬁes the same ﬁrst-

.

�

�

�

�

�

(b) Use item (a) to conclude that the reﬂexive transitive closure of a relation is not

ﬁrst-order deﬁnable.

2.4.6 Consider the class of square models for arrow logic. Observe that a square model
if we let each

� � � can be seen as a ﬁrst-order model �

� ��� � ����

� �

�

�

�

�

propositional variable � � � correspond to a dyadic relation symbol � .

�

�

�

(a) Work out this observation in the following sense. Deﬁne a suitable translation ���

�

mapping an arrow formula � to a formula �
� in this ‘dyadic correspondence
language’. Prove that this translation has the property that for all arrow formulas �
and all square models � the following correspondence holds:

� �

��

�

�

�

�

�

�

� ��

� �

�

�

� iff �

�

�

�� �

��

� �

���

� �

��

�

�

�

�

(b) Show that this translation can be done within the three variable fragment of ﬁrst-

order logic.

(c) Prove that conversely, every formula ���

� that uses only three variables, in a
ﬁrst-order language with binary predicates only, is equivalent to the translation of
an arrow formula on the class of square models.

� �

�

�

2.5 Modal Saturation via Ultraﬁlter Extensions

Bisimulations and the standard translation are two of the tools we need to under-
stand modal expressivity over models. This section introduces the third: ultraﬁlter
extensions. To motivate their introduction, we will ﬁrst discuss Hennessy-Milner
model classes and modally saturated models; both generalize ideas met in our ear-
lier discussion of bisimulations. We will then introduce ultraﬁlter extensions as a
way of building modally saturated models, and this will lead us to an elegant result:
modal equivalence implies bisimilarity-somewhere-else.

M-saturation

Theorem 2.20 tells us that bisimilarity implies modal equivalence, but we have
already seen that the converse does not hold in general (recall Figure 2.5). The
Hennessy-Milner theorem shows that the converse does hold in the special case of
image-ﬁnite models. Let’s try and generalize this theorem.

First, when proving Theorem 2.24, we exploited the fact that, between image-
ﬁnite models, the relation of modal equivalence itself is a bisimulation. Classes of
models for which this holds are evidently worth closer study.

92

2 Models

Deﬁnition 2.52 (Hennessy-Milner Classes) Let � be a modal similarity type, and
� a class of � -models. � is a Hennessy-Milner class, or has the Hennessy-Milner
property, if for every two models � and �
� of �
and �

� in � and any two states �, �

�, respectively, �

� implies �

�. �

�

� �

� �

�

�

�

For example, by Theorem 2.24, the class of image-ﬁnite models has the Hennessy-
Milner property. On the other hand, no class of models containing the two models
in Figure 2.5 has the Hennessy-Milner property.

We generalize the notion of image-ﬁniteness; doing so leads us to the concept of
modally-saturated or (brieﬂy) m-saturated models. Suppose we are working in the
� ��� �� � � be a model, let � be a state in � , and
basic modal language. Let �
� � � �� be an inﬁnite set of formulas. Suppose that � has successors
let � � ��
, . . . hold. If there is no
successor � of � where all formulas from � hold at the same time, then the model
is in some sense incomplete. A model is called m-saturated if incompleteness of
this kind does not occur.

, . . . where (respectively) �

, �

, �

, �

, �

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

�

�

�

�

To put it another way: suppose that we are looking for a successor of � at
� � � �� holds.
which every formula �
M-saturation is a kind of compactness property, according to which it sufﬁces to
ﬁnd satisfying successors of � for arbitrary ﬁnite approximations of �.

of the inﬁnite set of formulas � � ��

� �

�

�

�

� ��� �� � � be a model of the basic
Deﬁnition 2.53 (M-saturation) Let �
modal similarity type, � a subset of � and � a set of modal formulas. � is
satisﬁable in the set � if there is a state � � � such that �
� � �� � for all � in �;
� is ﬁnitely satisﬁable in � if every ﬁnite subset of � is satisﬁable in �.

The model � is called m-saturated if it satisﬁes the following condition for

every state � � � and every set � of modal formulas.

If � is ﬁnitely satisﬁable in the set of successors of �,
then � is satisﬁable in the set of successors of �.

The deﬁnition of m-saturation for arbitrary modal similarity types runs as follows.
Let � be a modal similarity type, and let � be a � -model. � is called m-saturated
� � and sequence
if, for every state � of � and every (�-ary) modal operator �

, . . . , �

�

of sets of modal formulas we have the following.

�

�

If for every sequence of ﬁnite subsets �
, . . . , �
states �
then there are states �
. �

such that ���

, . . . , �

and �
in � such that ���

� �

�

� � � �

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

, . . . , �
, . . . , �

�

�

�

�

�

�

,

there are

� �

�

and �

, . . . ,

�

�

� � � �

�

�

�

�

�

�

Proposition 2.54 Let � be a modal similarity type. Then the class of m-saturated
� -models has the Hennessy-Milner property.

2.5 Modal Saturation via Ultraﬁlter Extensions

93

�

�

� ��

Proof. We only prove the proposition for the basic modal language. Let �
� be two m-saturated models. It sufﬁces to prove
��� �� � � and �
that the relation � of modal equivalence between states in � and states in �
� is a
bisimulation. We conﬁne ourselves to a proof of the forth condition of a bisimula-
tion, since the condition concerning the propositional variables is trivially satisﬁed,
and the back condition is completely analogous to the case we prove.

� �

� �

�

�

�

�

� �

� are such that ��� and �

So, assume that �, � � � and �

�.
Let � be the set of formulas true at �. It is clear that for every ﬁnite subset � of
�, it follows that
� we have �
�. In
�; but, then, by
�. �

other words, � is ﬁnitely satisﬁable in the set of successors of �
m-saturation, � itself is satisﬁable in a successor �

�, hence �
� has an �

�-successor �

such that �

�. As �

�. Thus �

�, so �

� of �

�

�

�

� �

� �

�

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

Ultraﬁlter extensions

So the class of m-saturated models satisﬁes the Hennessy-Milner property — but
how do we actually build m-saturated models? To this end, we will now introduce
the last of the ‘big four’ model constructions: ultraﬁlter extensions. The ultraﬁlter
extension of a structure (model or frame) is a kind of completion of the original
structure. The construction adds states to a model in order to make it m-saturated.
Sometimes the result is a model isomorphic to the original (for example, when
the original model is ﬁnite) but when working with inﬁnite models, the ultraﬁlter
extension always adds lots of new points. power set algebra of a frame; we have
met this operation already in Section 1.4 when we introduced general frames, but
we repeat the deﬁnition here.

Deﬁnition 2.55 Let � be a modal similarity type, and �
For each �� � ��-ary relation �

, we deﬁne the following two operations �

a � -frame.
and

� ��� �

�

�

�

�

�

on the power set � �� � of � .

�

�

�

�

�

�

��

� � � � � �

�

�

�

�

�� �� � � � there exist �
and �

� � � �

��

�

�

� � � � � �

�

such that

for all ��

� �

�

�

��

� � � � � �

�

�

�

�

�

�

�� �� � � � for all �

� � � � � �

: if �

��

� � � �

,

�

�

�

�

�

�

�

�

then there is an � with �

� �

�� �

�

�

�� � is the set of points that ‘can see’ a state in �,
�� � is the set of points that ‘only see’ states in �. It follows that for any

�

In the basic modal language �
and �
model �

�

�

�

� �

�� � �

�

�� ���� and � �

�

�� � �

��� �����

�

Similar identities hold for modal operators of higher arity. Furthermore, �

and

�

are each other’s dual, in the following sense:

�

�

�

94

2 Models

Proposition 2.56 Let � be a modal similarity type, and �
frame. For every �-ary modal operator � and for every �-tuple �
subsets of � , we have

a � -
of

�

� � � � � �

�

� ��� �

�

�

�

�

�

�

�

��

� � � � � �

� � � � �

�� � �

� � � � � � � �

��

�

�

�

�

�

�

Proof. Left to the reader. �

We are ready to deﬁne ultraﬁlter extensions. As the name is meant to suggest, the
states of the ultraﬁlter extension of a model � are the ultraﬁlters over the universe
of �. Filters and ultraﬁlters are discussed in Appendix A. Readers that encounter
this notion for the ﬁrst time, are advised to make the Exercises 2.5.1–2.5.4.

�

� �� , �

Deﬁnition 2.57 (Ultraﬁlter Extension) Let � be a modal similarity type, and
a � -frame. The ultraﬁlter extension �� � of � is deﬁned as
�� � is the set of ultraﬁlters over � and
of ultraﬁlters over � if we have that

the frame �

. Here ��

�� �� �

� � � � � �

� � � �

��

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

�

�

�

�

�

�

�

��

� � � � � �

holds for a tuple �
whenever �

� � �

�

�

(for all � with � � � � �).

� �

�

�

�

�

�

�

The ultraﬁlter extension of a � -model �

� � � is the model �� �

�

�� �,

� �

� �

��

�

� where �

��

��

�

� is the set of ultraﬁlters of which � ��

� is a member. �

�

What are the intuitions behind this deﬁnition? First, note that the main ingredients
have a logical interpretation. Any subset of a frame can, in principle, be viewed as
(the extension or interpretation of) a proposition. A ﬁlter over the universe of the
frame can thus be seen as a theory, in fact as a logically closed theory, since ﬁlters
are both closed under intersection (conjunction) and upward closed (entailment).
Viewed this way, a proper ﬁlter is a consistent theory, for it does not contain the
empty set (falsum). Finally, an ultraﬁlter is a complete theory, or as we will call it,
a state of affairs: for each proposition (subset of the universe) an ultraﬁlter decides
whether the proposition holds (is a member of the ultraﬁlter) or not.

How does this relate to ultraﬁlter extensions? In a given frame � not every state
of affairs need be ‘realized’, in the sense that there is a state satisfying all and
only the propositions belonging to the state of affairs; only the states of affairs that
correspond to the principal ultraﬁlters are realized, namely, as the points of the
frame. We build �� � by adding every state of affairs for � as a new element of the
domain — that is, �� � realizes every proposition in �.

How should we relate these new elements in �� � to each other and to the original

elements from �? The obvious choice is to stipulate that �
‘sees’ the �-tuple �

. That is, whenever �

, . . . , �

if �
are propositions of
, . . . , �
‘sees’ this combination: that is, the proposition
�� is self-

. The deﬁnition of the valuation �

� � � �

��

�

�

�

�

�

�

�

�

, . . . , �

respectively, then �

�

�

�

�

�

�

� is a member of �

�

�

��

� � � � � �

�

�

�

explanatory.

2.5 Modal Saturation via Ultraﬁlter Extensions

95

One ﬁnal comment: a special role in this section is played by the so-called prin-
cipal ultraﬁlters over � . Recall that, given an element � � � , the principal
ultraﬁlter �
generated by � is the ﬁlter generated by the singleton set ���: that
� �� � � � � � � �. By identifying a state � of a frame � with the prin-
is, �
, it is easily seen that any frame � is (isomorphic to) a submodel
cipal ultraﬁlter �
(but in general not a generated submodel) of its ultraﬁlter extension. For we have
the following equivalences (here proved for the basic modal similarity type):

�

�

�

���

iff � � �

�

�� � for all � � � such that � � �

iff �

�

�� � � �

for all � � � such that � � �

(2.1)

�

�

iff �

��

�

�

�

�

�

Let’s make our discussion more concrete by considering an example.

Example 2.58 Consider the frame �
ordering):

� �� (the natural numbers in their usual

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

. . .

�

�

�

�

�

What is the ultraﬁlter extension of �? There are two kinds of ultraﬁlters over an
inﬁnite set: the principal ultraﬁlters that are in 1–1 correspondence with the points
of the set, and the non-principal ones which contain all co-ﬁnite sets, and only
inﬁnite sets, cf. Exercise 2.5.4. We have just remarked (see (2.1)) that the principal
ultraﬁlters form an isomorphic copy of the frame � inside �� �. So where are
the non-principal ultraﬁlters situated? The key fact here is that for any pair �, �
� of
� be a non-principal
ultraﬁlters, if �
� there is an � such that
ultraﬁlter, and let � � �
� � � and � � �. This shows that �
�. But � is an element of every
ultraﬁlter �.

�. As � is inﬁnite, for any � �

� is non-principal, then �

�. To see this, let �

�� � �

��

��

�

This shows that the ultraﬁlter extension of � looks like a gigantic balloon at the
end of an inﬁnite string: it consists of a copy of �, followed by an large (uncount-
able) cluster consisting of all the non-principal ultraﬁlters:

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

. . .

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

We will prove two results concerning ultraﬁlter extensions. The ﬁrst one, Proposi-
tion 2.59, is an invariance result: any state in the original model is modally equiv-
alent to the corresponding principal ultraﬁlter in the ultraﬁlter extension. Then, in
Proposition 2.61 we show that ultraﬁlter extensions are m-saturated. Putting these
two facts together leads us to the main result of this section: two states are modally
equivalent iff their representatives in the ultraﬁlter extensions are bisimilar.

�

�

96

2 Models

Proposition 2.59 Let � be a modal similarity type, and � a � -model. Then, for
any formula � and any ultraﬁlter � over � , � ��� � � iff �� �
�. Hence, for
every state � of � we have �

.

�

� �

�

�

�

Proof. The second claim of the proposition is immediate from the ﬁrst one by the
observation that �

� iff � � � ��� iff � ��� � �

.

�

The proof of the ﬁrst claim is by induction on �. The basic case is immediate
from the deﬁnition of �
��. The proofs of the boolean cases are straightforward
consequences of the deﬁning properties of ultraﬁlters. As an example, we treat
negation; suppose that � is of the form ��, then

�

� ���� � �

iff � � � ��� � �
iff
iff
iff

� ��� �� �

�� �

�� �

�� �

� � �

� �

�

�

�

(induction hypothesis)

� (we only treat the basic modal
Next, consider the case where � is of the form �
similarity type, leaving the general case as an exercise to the reader). Assume ﬁrst
that �� �
�. The induction hypothesis implies that � ��� � �

��,
�� ���� � �. Now the result follows immediately from the observation that

�. Then, there is an ultraﬁlter �

�, so by the deﬁnition of �

� such that �

� and �� �

�

�

��

� �

� �

��

�

�

�

�

�

�� ���� � � �

�

��.

�

The left-to-right implication requires a bit more work. Assume that � �

We have to ﬁnd an ultraﬁlter �
straint reduces to the condition that �
(see Exercise 2.5.5):

� such that � ��� � �

� and �

��

��

�� � � � whenever � � �

�

�

�� � �.
�. The latter con-
�, or equivalently

�

�

�

�

�� �� � �

��� � � �� � �

�

�

We will ﬁrst show that �
. By deﬁnition, �

�

�

�

�

��� � and �

�

is closed under intersection. Let � , � be members of
��� � � � � �, as
��� �, as a straightforward proof shows. This proves

��� � are in �. But then �

�

�

�

��� � � �

�

�

�

�

��� � � � � �

that � � � � �

�

.

�

Next we make sure that for any � � �

�. Let � be an ar-
�� � � �. As � is closed
bitrary element of �
under intersection and does not contain the empty set, there must be an element
��. But then � must have a successor � in � ���. Finally,
� in �

, then by deﬁnition of �

, � � � ��� ��

, �

��� � � � �

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

�� � implies � � � .

�

�

�

�

�

�, it follows that the set �

¿From the fact that �
, � � � ��� ��

is closed under intersection, and the fact that for any � �
� �� ���� has the ﬁnite intersection
property. So the Ultraﬁlter Theorem (Fact A.14 in the Appendix) provides us with
� has the desired
�. This ultraﬁlter �
an ultraﬁlter �
� follows
properties: it is clearly a successor of �, and the fact that �� �
� and the induction hypothesis. �
from � ��� � �

� such that �

� �� ���� � �

� �

�

�

�

�

�

�

2.5 Modal Saturation via Ultraﬁlter Extensions

97

Example 2.60 As with the invariance results of Section 2.1 (disjoint unions, gen-
erated submodels, and bounded morphisms), our new invariance result can be used
to compare the relative expressive power of modal languages. Consider the modal
constant � whose truth deﬁnition in a model for the basic modal language is

� � iff �

�� ����� � for some � in �.

�

� �

Can such a modality be deﬁned in the basic modal language? No — a bisimulation
based argument given at the end of the previous section already establishes this.
� �� and
Alternatively, we can see this by comparing the pictures of the frames �
its ultraﬁlter extension given in Example 2.58. The former is loop-free (thus in any
model over this frame, �� �
� �), but the later contains uncountably many
loops (thus �� �

� �). So if we want � we have to add it as a primitive. �

� �

� �

�

�

�

Proposition 2.61 Let � be a modal similarity type, and let � be a � -model. Then
�� � is m-saturated.

�

Proof. We only prove the proposition for the basic modal similarity type. Let
� ��� �� � � be a model; we will show that its ultraﬁlter extension �� � is m-
saturated. Consider an ultraﬁlter � over � , and a set � of modal formulas which
is ﬁnitely satisﬁable in the set of successors of �. We have to ﬁnd an ultraﬁlter �
such that �

� and �� �

�. Deﬁne

��

� �

��

�

�

�

� � �� ��� � � � �

� � �� � �

��� � � ���

�

�

�

� and �� � �

� is the set of (ﬁnite) conjunctions of formulas in �. We claim that the set
�� � � �� are closed
� and an arbitrary
�, then
�, or, in other
�� by Exercise 2.5.5. Hence,
�� and, therefore, cannot be identical to

where �
� has the ﬁp. Since both �� ��� � � � �
under intersection, it sufﬁces to prove that for an arbitrary � � �
set � � � for which �
by assumption, there is a successor �
words, � ��� � �
� ��� � � is an element of the ultraﬁlter �
the empty set.

��� � � �, we have � ��� � � ��

�� � � � implies � � �

�� of � such that �� �

�. But if � � �

��. Then, �

� �

�

�

�

��

�

�

�

�.
It follows by the Ultraﬁlter Theorem that � can be extended to an ultraﬁlter �

Clearly, �

� is the required successor of � in which � is satisﬁed. �

We have ﬁnally arrived at the main result of this section: a characterization of
modal equivalence as bisimilarity-somewhere-else — namely, between ultraﬁlter
extensions.

Theorem 2.62 Let � be a modal similarity type, and let � and �
and �, �

� two states in � and �

�, respectively. Then

� be � -models,

�

�

�

� �

� �

�

� iff �� �

� �

� �

�

�

�

�

�� �

�

�

�
98

2 Models

Proof. Immediate by Propositions 2.59, 2.61 and 2.54. �

Three remarks. First, it is easy to deﬁne ultraﬁlter extensions and prove an analog
of Theorem 2.62 for the basic temporal logic and arrow logic; see Exercises 2.5.8
and 2.5.9. With PDL the situation is a bit more complex; see Exercise 2.5.11. (The
problem is that the property of one relation being the reﬂexive transitive closure
of another is not preserved under taking ultraﬁlter extensions.) Second, we have
not seen the last of ultraﬁlter extensions. Like disjoint unions, generated submod-
els, and bounded morphisms, ultraﬁlter extensions are a fundamental modal model
construction technique, and we will make use of them when we discuss frames (in
Chapter 3) and algebras (in Chapter 5). We will shortly see that ultraﬁlter exten-
sions tie in neatly with ideas from ﬁrst-order model theory — and we will use this
to prove a second bisimilarity-somewhere-else result, Lemma 2.66. Finally, some
readers may still have the feeling that taking the ultraﬁlter extension of a model is
a far less natural construction than the other model operations that we have met.
These readers are advised to hold on until (or take a peek ahead towards) Chapter 5,
where we will see that ultraﬁlter extensions are indeed a very natural byproduct of
modal logic’s duality theory.

Exercises for Section 2.5
2.5.1 Let � be any subset of � �� �, and let � be the ﬁlter generated by �.

(a) Prove that indeed, � is a ﬁlter over � . (Show that in general, the intersection of a

collection of ﬁlters is again a ﬁlter.)

(b) Show that � is the set of all � � � �� � such that either � � � or for some �

�,

. . . , �

�

� �,

(c) Prove that � is proper (that is: it does not coincide with � �� �) iff � has the ﬁnite

intersection property.

�

�

� � � � � �

� ��

�

2.5.2 Let � be a non-empty set, and let � be an element of � . Show that the principal
ultraﬁlter generated by �, that is, the set �� � � �� � � � � � �, is indeed an ultraﬁlter
over � .

2.5.3 Let � be a ﬁlter over � .

(a) Prove that � is an ultraﬁlter if and only if it is proper and maximal, that is, it has

no proper extensions.

(b) Prove that � is an ultraﬁlter if and only if it is proper and for each pair of subsets

�� � of � we have that � � � � � iff � � � or � � � .

2.5.4 Let � be an inﬁnite set. Recall that � � � is co-ﬁnite if � � � is ﬁnite.

(a) Prove that the collection of co-ﬁnite subsets of � has the ﬁnite intersection prop-

erty.

(b) Show that there are ultraﬁlters over � that do not contain any ﬁnite set.

2.5 Modal Saturation via Ultraﬁlter Extensions

99

(c) Prove that an ultraﬁlter is non-principal if and only if it contains only inﬁnite sets

if and only if it contains all co-ﬁnite sets.

(d) Prove that any ultraﬁlter over � has uncountably many elements.

2.5.5 Given a model �

� ��� �� � � and two ultraﬁlters � and � over � , show that

��

�

�� if and only if �� � �

�� � � �� � �.

�

�

2.5.6 Let �
� �� � �� be the transitive binary tree; that is, � is the set of ﬁnite strings of
�s and �s, and ��� holds if � is a proper initial segment of � . The aim of this exercise is
to prove that any non-principal ultraﬁlter over � determines an inﬁnite string of �s and �s.
� the relation

� be the set of ﬁnite and inﬁnite strings of 0s and 1s, and �

To this end, let �

� given by ��� if � is an initial segment of � . Deﬁne a function � �

on �
such that for all ultraﬁlters over � we have ��

��

� iff � ����

�

� ���.

��

�� � � �

�

2.5.7 Give an example of a model � which is point-generated while its ultraﬁlter exten-
sion is not.

2.5.8 Develop a notion of ultraﬁlter extension for basic temporal logic, and establish an
analog of Theorem 2.62 for basic temporal logic.

2.5.9 Develop a notion of ultraﬁlter extension for the arrow language introduced in Exam-
ple 1.14, and establish an analog of Theorem 2.62 for this language.

2.5.10 Show that, in general, ﬁrst-order formulas are not preserved under ultraﬁlter ex-
tensions. That is, give a model �, a state �, and a ﬁrst-order formula ���� such that
is the principal ultraﬁlter generated by

�� �������, but �� �

�, where �

��� ������

�

�.

�

�

2.5.11 Consider a modal similarity type with two diamonds, � and ���, and take any
model �

� � � with

� ��� �� �

�

� �

� ����

�

� � ��� � �� ��� ��� �� � � �

��

�

�

� ���� �� � �� � �

� � � �� � ���� � � ��

�

�

Note that �

� is the reﬂexive transitive closure of �.

(a) Show that �
(b) Let � be an arbitrary non-principal ultraﬁlter over �. Prove that �
(c) Let � be an arbitrary non-principal ultraﬁlter over �. Prove that � has an �

�.

�.

� �

���

��

�

�

�

�

�

��-
��-successors is again a non-principal

successor in �� �, and that each of its �
ultraﬁlter.

(d) Now suppose that we add an new diamond ��� to the language, and that in the
��. Show that

to be the reﬂexive transitive closure of �

model �� � we take �

�� �

�

� �

���

�

�

�

�

�.

(e) Prove that �

��

�

�� �

�

(hint: use Proposition 2.59), and conclude that the ultraﬁlter

extension of a regular PDL-model need not be a regular PDL-model.

(f) Prove that every non-principal ultraﬁlter over � has a unique �

��-successor.

100

2 Models

2.6 Characterization and Deﬁnability

In Section 2.3 we posed two important questions about modal expressivity:

(i) What is the modal fragment of ﬁrst-order logic? That is, which ﬁrst-order
formulas are equivalent to the standard translation of a modal formula?
(ii) Which properties of models are deﬁnable by means of modal formulas?

In this, the ﬁrst advanced track section of the book, we answer both questions. Our
main tool will be a second characterization of modal equivalence as bisimilarity-
somewhere-else, the Detour Lemma. Unlike the characterization just proved (The-
orem 2.62), the Detour Lemma rests on a number of non-modal concepts and re-
sults, all of which are centered on saturated models (a standard concept of ﬁrst-
order model theory). We start by introducing saturated models and use them to
describe the modal fragment of ﬁrst-order logic. After that we show how to build
saturated models. As corollaries we obtain results on modally deﬁnable proper-
ties of models. For background information on ﬁrst-order model theory, see Ap-
pendix A.

The Van Benthem Characterization Theorem
To deﬁne the notion of saturated models, we need the concept of �-saturation, but
before giving a formal deﬁnition of the latter, we provide an informal description,
which the reader may want to use as a ‘working’ deﬁnition.

Informally, then, the notion of �-saturation can be explained as follows. First of
all, let � ��� be a set of ﬁrst-order formulas in which a single individual variable �
may occur free — such a set of formulas is called a type. A ﬁrst-order model �
realizes � ��� if there is an element � in � such that for all � � � , �

�� � ���.

Next, let � be a model for a given ﬁrst-order language �

For a subset � � � , �
constants � for all elements � � �. �

�

��� is the language obtained by extending �

� with domain � .
� with new
is the expansion of � to a structure for

�

�

�

�

�

�

, �

�. Let � ��

���; it is not difﬁcult to see that � ��

��� in which each � is interpreted as �.
Assume that � is of size at most �. For the sake of our informal deﬁnition
� �� be a
� �� is consistent
, (that
� ��). So, for this particular set
� �� is ﬁnitely realizable in

of �-saturation, assume that � � � and � � ��
type of the language �
with the ﬁrst-order theory of �
is, �

realizes every ﬁnite subset � of � ��
� ��, �-saturation of � means that if � ��
� �� is realizable in �

.
Yet another way of looking at �-saturation for this particular set of formulas is
� �� be the formula
,

the following. Consider a formula � ��
with the fresh variables �
respectively. Then we have the following equivalence:

replacing each occurrence in � of �

� �� is ﬁnitely realizable in �

� ��, and let � ��

, then � ��

iff � ��

and �

and �

�

�

�

�

� ��

�

� �

� �

� �

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

2.6 Characterization and Deﬁnability

realizes �� ��

� �

� ��� iff there is a � such that �

�

�

�

�

�� � ��

� �

� ����

� �

�

�

�

�

101

� ��.

So, a model is �-saturated iff the following holds for every � � �, and every set �
of formulas of the form � ��

� ��.

� � � � � �

�

�

� is an �-tuple such that for every ﬁnite � � � there is a �

� for every � � �,

� �

�

�

�

�

�

� � � � � �

If ��
such that �
then we have that there is a � such that �
for every � � � .

� � � � � �

� � � � � �

�� � ��

� ����

�

�

�

�� � ��

� � � � � �

� ����

� � � � � �

� ��

�

�

�

�

This way of looking at �-saturation is useful, for it makes the analogy with m-
saturation of the previous section clear. Both m-saturated and countably saturated
models are rich in the number of types � ��� they realize, but the latter are far richer
than the former: they realize the maximum number of types.

Now, for the ‘ofﬁcial’ deﬁnition of �-saturation.

Deﬁnition 2.63 Let � be a natural number, or �. A model � is �-saturated if for
every subset � � � of size less than �, the expansion �
realizes every set � ���
of �
���-formulas (with only � occurring free) that is consistent with the ﬁrst-order
theory of �

. An �-saturated model is usually called countably saturated. �

�

�

�

Example 2.64 (i) Every ﬁnite model is countably saturated. For, if � is ﬁnite,
and � ��� is a set of ﬁrst-order formulas consistent with the ﬁrst-order theory of
�, there exists a model � that is elementarily equivalent to � and that realizes
� ���. But, as � and � are ﬁnite, elementary equivalence implies isomorphism,
and hence � ��� is realized in �.

�

(ii) The ordering of the rational numbers �

The relevant ﬁrst-order language �
let � ��� be a set of formulas in the resulting expansion �
language that is consistent with the theory of �
model � of the theory of �
elementary submodel �

� �� is countably saturated as well.
� has � and �. Take a subset � of � and
��� of this ﬁrst-order
. Then, there exists a
that realizes � ���. Now take a countable
� of � that contains at least one object realizing � ���. Then
� is a countable dense linear ordering without endpoints, and hence the ordering
� ��. The interpretations (in �) of the constants � for
�. Hence, as � realizes � ���, so does

of �
elements � in � may be copied across to �
� ��, as required.

� is isomorphic to �

� �� ��

� �� ��

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

�, and hence, so does �
(iii) The ordering of the natural numbers �
see this, consider the following set of formulas.

�

� �� is not countably saturated. To

� ���

�� ���

��

� ��� � � � � ��

� � � �

��

� � � � � �

� ��� � � ���

�

�

�

�

�

�

� ��� is clearly consistent with the theory of �
realizable in �

� ��. Yet, � ��� is clearly not realizable in �

� �� as each of its ﬁnite subsets is
� ��. �

�

�

�

102

2 Models

The following result explains why countably saturated models matter to us.

Theorem 2.65 Let � be a modal similarity type. Any countably saturated � -model
is m-saturated. It follows that the class of countably saturated � -models has the
Hennessy-Milner property.

Proof. We only consider the basic modal language. Assume that �
� ��� �� � �,
viewed as a ﬁrst-order model, is countably saturated. Let � be a state in � , and
consider a set � of modal formulas which is ﬁnitely satisﬁable in the successor set
of �. Deﬁne �

� to be the set

�

�

� ����� �

�� ��

��

�

�

�

��

�� � is the set �

where ��
in �. Clearly, �
ﬁnite subset of �
� itself is realized in some state �. By �
of �, �
successor of �. Then, by Theorem 2.47 and the fact that �
� � �, it follows that �

��� � � � � � of standard translations of formulas
� is consistent with the ﬁrst-order theory of �
realizes every
�, namely in some successor of �. So, by the countable saturation
�� ������ it follows that � is a
������ for all

�. Thus � is satisﬁable in a successor of �. �

: �

�� ��

� �

�

�

�

�

�

�

In fact, we only need 2-saturation for the proof of Theorem 2.65 to go through.
This is because we restricted ourselves to the basic modal similarity type. We
leave it to the reader to check to which extent the ‘amount of saturation’ needed to
make the proof of Theorem 2.65 go through depends on the rank of the operators
of the similarity type.

We have yet to show that countably saturated models actually exist; this issue
will be addressed below (see Theorem 2.74). For now, we merely want to record the
following important use of saturated models; you may want to recall the deﬁnition
of an elementary embedding before reading the result (see Appendix A)).

Lemma 2.66 (Detour Lemma) Let � be a modal similarity type, and let � and
� be � -models, and � and � states in � and �, respectively. Then the following
are equivalent.

(i) For all modal formulas �: �
(ii) There exists a bisimulation � �
(iii) There exist countably saturated models �

� iff �

�� �

� �

� �

�

�

�.

� �

�

�

�� �

.
� and �

� �

�

�

�

� �

� and elementary

� �

embeddings � �

� and � �

�

� such that

�

�

�

�

�

(a) � ��� � �
(b) �

� �

�

�

� and ���� � �
�.

� �

�

�

�

�

What does the Detour Lemma say in words? Obviously (i) � (ii) is just our old
bisimulation-somewhere-else result (Theorem 2.62). The key new part is the im-
� � are modally equivalent, then
plication (i) � (iii). This says that if �

� � and �

2.6 Characterization and Deﬁnability

103

�

�

�

�

� �

� �

� �

� �

� and �

�. As �

� � and �

both can be extended — more accurately: elementarily extended — to countably
� and �
� � were modally equivalent,
saturated models �
so are �
�; it follows by Theorem 2.65 that the latter two models
are bisimilar. In short, this is a second ‘bisimilarity somewhere else’ result, this
time the ‘somewhere else’ being ‘in some suitable ultrapower’. Notice that in or-
der to prove the Detour Lemma all we need to establish is that every model can be
elementarily embedded in a countably saturated model — there are standard ﬁrst-
order techniques for doing so, and we will introduce one in the second half of this
section.

With the help of the Detour Lemma, we can now precisely characterize the
relation between ﬁrst-order logic, modal logic, and bisimulations. To prove the
theorem we need to explicitly deﬁne a concept which we have already invoked
informally on several occasions.

is invariant for bisimulations if
Deﬁnition 2.67 A ﬁrst-order formula ���� in �
for all models � and �, and all states � in �, � in �, and all bisimulations �
between � and � such that �� �, we have �

�� ������� iff �

�� ������ �. �

�

�

Theorem 2.68 (Van Benthem Characterization Theorem) Let ���� be a ﬁrst-
. Then ���� is invariant for bisimulations iff it is (equivalent
order formula in �
to) the standard translation of a modal � -formula.

�

�

Proof. The direction from right to left is a consequence of Theorem 2.20. To prove
the direction from left to right, assume that ���� is invariant for bisimulations and
consider the set of modal consequences of �:

������ � �

��

�

��� � � is a modal formula, and ���� ��

��

�

�����

Our ﬁrst claim is that if ������ �� ����, then ���� is equivalent to the translation
of a modal formula. To see why this is so, assume that ������ �� ����; then,
by the Compactness Theorem for ﬁrst-order logic, for some ﬁnite subset � �
�,
������ we have � �� ����. So ��
�. And as every � � � is the translation of a modal formula,
thus �� ���� �
so is

� � ����. Trivially �� ���� �

�. This proves our claim.

�

�

So it sufﬁces to show that ������ �� ����. Assume �

�� ���������; we

�

�

need to show that �

�� �������. Let

� ��� � �

��� �

��

��������

�

�

��

��

�

We claim that � ��� � ������ is consistent. Why? Assume, for the sake of con-
tradiction, that � ��� � ������ is inconsistent. Then, by compactness, for some
ﬁnite subset �
������. But this implies �
and �

��� � � ��� we have �� ���� � �

������, which contradicts �

���. Hence �

�� � ������.

��� � � ���

��� �

�� �

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

104

2 Models

�

� �

� implies ��

So, let �

� � be such that �

�� � ��� � �������� �. Observe that � and � are
�;
��. If modal equivalence
� � would be

modally equivalent: �
and likewise, if �
� then �
implied bisimilarity we would be done, because then �
bisimilar, and from this we would be able to deduce the desired conclusion �
������� by invariance under bisimulation. But, in general, modal equivalence does
not imply bisimilarity, so this is not a sound argument.

��� � � ���, which implies �

��, and �

� � and �

� � �

� �

� �

� �

�

�

�

�

�

� � ��

However, we can use the Detour Lemma and make a detour through a Hennessy-
Milner class where modal equivalence and bisimilarity do coincide! More pre-
cisely, the Detour Lemma yields two countably saturated models �
and �

� � such that �

�:

� �

� �

� �

�

�

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

� �

� �

�

�

�

This is where we really need the new characterization of modal equivalence in
terms of bisimulation-somewhere-else that Theorem 2.74 gives us. We need to
‘lift’ the ﬁrst-order formula ���� from the model �
�. By
deﬁnition, the truth of ﬁrst-order formulas is preserved under elementary embed-
dings, so that this can indeed be done. However, ﬁrst-order formulas need not be
preserved under ultraﬁlter extensions (see Exercise 2.5.10), and for that reason we
cannot use the ultraﬁlter extension �� �
Returning to the main argument, �

�.
�� ������ � implies �

� � to the model �

instead of �

�� ������

� �

� �

� �

�

�

�

�

�

���� is invariant for bisimulations, we get �
elementary embeddings, we have �

�

�� ������

�

�� �������. This proves the theorem. �

�. As
�. By invariance under

Ultraproducts

The preceding discussion left us with an important technical question: how do
we get countably saturated models? Our next aim is to answer this question and
thereby prove the Detour Lemma.

The fundamental construction underlying our proof is that of an ultraproduct.
Here we brieﬂy recall the basic ideas; further details may be found in Appendix A.
�, � is

We ﬁrst apply the construction to sets, and then to models. Suppose � ��

an ultraﬁlter over �, and for each � � �, �
be the Cartesian product of those sets. That is: � is the set of all functions � with
. For two functions � , � � � we say
domain � such that for each � � �, � ��� � �
that � and � are � -equivalent (notation � �
�) if �� � � � � ��� � ����� � � .
The result is that �

is an equivalence relation on the set �.

is a non-empty set. Let � �

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

2.6 Characterization and Deﬁnability

105

Deﬁnition 2.69 (Ultraproduct of Sets) Let �
ulo �
the set of all equivalence classes of �

, that is: �

� �� � � � � �

�

�

�

�

be the equivalence class of � mod-
modulo � is

� �. The ultraproduct of �
. So
. it is denoted by

�

�

�

�

�

�

� ��

� � �

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

In the case where all the sets are the same, say �
is called the ultrapower of � modulo � , and written

�

�

�

� . �

�

� � for all �, the ultraproduct

Following the general deﬁnition of the ultraproduct of ﬁrst-order models (Deﬁni-
tion A.17), we now deﬁne the ultraproduct of modal models.

�

Deﬁnition 2.70 (Ultraproduct of Models) Fix a modal similarity type � , and let
modulo � is the model

(� � �) be � -models. The ultraproduct

of �

�

�

�

�

�

described as follows.

�

�

(i) The universe �

of

is the set

�

, where �

is the universe of

�

�

�

�

�

�

�

.

�

�

(ii) Let �
by

�

be the valuation of �

. Then the valuation �

of

is deﬁned

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

��� iff �� � � � � ��� � �

�

�

�

���� � ��

(iii) Let � be a modal operator in � , and �

its associated relation in the model

. The relation �

�

in

�

�

is given by

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

� � � �

�

iff �� � � � �

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

��� � � � �

���� � ��

In particular, for a diamond item (iii) boils down to

�

�

�

�

iff �� � � � �

�

�

�

�

�

� �������� � �� �

To show that the above deﬁnition is consistent, we should check that �
depend only on the equivalence classes �

, . . . , �

.

��

�

�

�

and �

�

Proposition 2.71 Let
� we have �
that �

� �

�

� iff

��� � �, for all � � �.

�

�

�

� be an ultrapower of �. Then, for all modal formulas
is the constant function such

�, where �

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

Proof. This is left as Exercise 2.6.1. �

To build countably saturated models, we use ultraproducts based on a special kind
of ultraﬁlters. An ultraﬁlter is countably incomplete if it is not closed under count-
able intersections (of course, it will be closed under ﬁnite intersections).

106

2 Models

Example 2.72 Consider the set of natural numbers �. Let � be an ultraﬁlter over
� that does not contain any singletons ���. (The reader is asked to prove that such
ultraﬁlters exist in Exercise 2.5.4.) Then, for all �, �

� ���� � � . But

�

So � is countably incomplete. �

�

�

�

�

�

� ���� �� ��

�

�

�

Lemma 2.73 Let � be a countable ﬁrst-order language, � a countably incomplete
ultraﬁlter over a non-empty set �, and � an �-model. The ultrapower
� is
countably saturated.

�

�

Proof. See Appendix A. �

We are now ready to prove the Detour Lemma. In Theorem 2.62 we showed that
‘bisimulation somewhere else’ can mean ‘in the ultraﬁlter extension’. Now we will
show that it can also mean: ‘in a suitable ultrapower of the original models.’

Theorem 2.74 Let � be a modal similarity type, and let � and � be � -models,
and � and � states in � and �, respectively. Then the following are equivalent.

(i) For all modal formulas �: �
(ii) There exist ultrapowers

� iff �

� �

�

�.

� �

�

� and

� and as well as a bisimulation

and ��
) is the constant function mapping every index to � (�).

linking ��

� ��

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

� �

(�

, where �

�

�

�

�

�

�

�

�

�

Proof. It is easy to see that (ii) implies (i). By Proposition 2.71 �

� �

�

�

� ��

�

�

�

�. By assumption this is equivalent to

�

�

�

�

� ��

�

�

�

�

� iff
�, and

the latter is equivalent to �

� �

�.

�

�

�

To prove the implication from (i) to (ii) we have to do some more work. Assume
�. We need to create

� iff �

� �

� �

�

�

that for all modal formulas � we have �
bisimilar ultrapowers of � and �.

�

�

�

� and

� are countably saturated. Now ��

Take the set of natural numbers � as our index set, and let � be a countably
incomplete ultraﬁlter over � (cf. Example 2.72). By Lemma 2.73 the ultrapowers
are modally
equivalent: for all modal formulas �,
�.
This claim follows from the assumption that � and � are modally equivalent to-
are
gether with Proposition 2.71. Next, apply Theorem 2.65: as ��
� are countably saturated, there exists a
� and
modally equivalent and
bisimulation � �

. This proves the theorem. �

and ��

and ��

� iff

� ��

� ��

� ��

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

We obtain the Detour Lemma as an immediate corollary of Theorem 2.74 and
Theorem 2.62.

�

�

2.6 Characterization and Deﬁnability

107

Deﬁnability
Our next aim is to answer the second of the two questions posed at the start of this
section: which properties of models are deﬁnable by means of modal formulas?
Like the Detour Lemma, the answer is a corollary of Theorem 2.74. We formulate
the result in terms of pointed models. Given a modal similarity type � , a pointed
� �� where � is a � -model and � is a state of �. Although
model is a pair �
the results below can also be given for models, the use of pointed models allows
for a smoother formulation, mainly because pointed models reﬂect the local way
in which modal formulas are evaluated.

�

�

We need some further deﬁnitions. A class of pointed models � is said to be
closed under bisimulations if �
� �� in
� �� in � and �
�. � is closed under ultraproducts if any ultraproduct
� of a family of
pointed models �
� in � belongs to �. If � is a class of pointed � -models, �
denotes the complement of � within the class of all pointed � -models. Finally, � is
deﬁnable by a set of modal formulas if there is a set of modal formulas � such that
�;
for any pointed model �
� is deﬁnable by a single modal formula iff it is deﬁnable by a singleton set.

� �� in � iff for all � � � , �

� �� we have �

� � implies �

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

�

�

�

�

�

�

�

By Proposition 2.47 deﬁnable classes of pointed models must be closed under
bisimulations, and by Corollary A.20 they must be closed under ultraproducts as
well. Theorems 2.75 and 2.76 below show that these two closure conditions sufﬁce
to completely describe the classes of pointed models that are deﬁnable by means
of modal formulas.

Theorem 2.75 Let � be a modal similarity type, and � a class of pointed � -models.
Then the following are equivalent.

(i) � is deﬁnable by a set of modal formulas.
(ii) � is closed under bisimulations and ultraproducts, and � is closed under

ultrapowers.

Proof. The implication from (i) to (ii) is easy. For the converse, assume � and �
satisfy the stated closure conditions. Observe that � is closed under bisimulations,
as � is. Deﬁne � as the set of modal formulas holding in �:

� � �� � for all �

� �� in �: �

�

� �

���

�

We will show that � deﬁnes the class �. First of all, by deﬁnition every pointed
� . Second,
model �
assume that �
must be in �.

� ; to complete the proof of the theorem we show that �

� �� in � is a model satisfying � in the sense that �

� ��

� �

� �

�

�

�

�

Deﬁne � to be the modal theory of �; that is, � � �� �

�

� �

�

��. It is

obvious that � is ﬁnitely satisﬁable in �; for suppose that the set ��
� is not satisﬁable in �. Then the formula ���

� � � � � �

�

�

�

� � � � � �

� �

�

� would be true on all

108

2 Models

� �. But then the
pointed models in �, so it would belong to � , yet be false in �
following claim shows that � is satisﬁable in the ultraproduct of pointed models
in �.

Claim 1 Let � be a set of modal formulas, and � a class of pointed models in
which � is ﬁnitely satisﬁable. Then � is satisﬁable in some ultraproduct of models
in �.

Proof of Claim. Deﬁne an index set � as the collection of all ﬁnite subsets of �:

� � ��

� � � �

�

�

is ﬁnite��

By assumption, for each � � � there is a pointed model �

� in � such that
�. We now construct an ultraﬁlter � over � such that the ultraproduct

� �

�

�

�

�

�

� �

�

�

�

has a state �
For each � � �, let

�

�

�

with

�

�

� �

�

�

�

�.

� be the set of all � � � such that � � �. Then the set

�

�

� � � � � � has the ﬁnite intersection property because

� � �

�

�

�

�

�

�

��

� � � � � �

� �

�

� � � � �

�

�

So, by Fact A.14, � can be extended to an ultraﬁlter � over �. This deﬁnes
for the deﬁnition of �
the function � �

denote the universe of the model �

such that � ��� � �

, let �

.

;
and consider

�

�

�

�

�

�

�

�

�

It is left to prove that

�

�

�

�

�

�

�

�

� �

� �

�

�

�

�

(2.2)

To prove (2.2), observe that for � �
for each � � �

�

� we have � � �, and so �

� �

�

�. Therefore,

�

�

�� � � �

� �

�� �

�

�

�

�

�

� and

� � � �

It follows that �� � � �
This proves (2.2).

�

�

� �

�

�� � � , so by Theorem A.19,

�

� �

�

�.

�

�

�

�

�

�

�

�

It follows from Claim 1 and the closure of � under taking ultraproducts that � is
� implies that � and
satisﬁable in some pointed model �
� �� are modally equivalent. So by
the state � from our original pointed model �
Theorem 2.74 there exists an ultraﬁlter �

� �� in �. But �

� such that

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

� ��� ��

�

�

� ��� ��

�

�

�

�

�

�

�

�

�

By closure under ultraproducts, the pointed model �
�. Hence by closure under bisimulations, �
closure of � under ultrapowers it follows that �
proof. �

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

� ��� ��

� belongs to
� is in � as well. By
� �� is in �. This completes the

� ��� ��

�

�

�

�

�

�

�

2.6 Characterization and Deﬁnability

109

Theorem 2.76 Let � be a modal similarity type, and � a class of pointed � -models.
Then the following are equivalent.

(i) � is deﬁnable by means of a single modal formula.
(ii) Both � and � are closed under bisimulations and ultraproducts.

Proof. The direction from (i) to (ii) is easy. For the converse we assume that �,
� satisfy the stated closure conditions. Then both are closed under ultraproducts,
hence by Theorem 2.75 there are sets of modal formulas �
deﬁning � and
�, respectively. Obviously their union is inconsistent in the sense that there is no
. So then, by compactness,
pointed model �
such that for all pointed models
there exist �

� �� such that �
and �

, . . . , �

, �

� � � � � �

� ��

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

�

�

� ��

�

�

� �

�

� � � � � �

� ��

� � � � � ��

�

�

�

�

�

(2.3)

To complete the proof we show that � is in fact deﬁned by the conjunction �

�

�

� � � � �

�

. By deﬁnition, for any �

�

Conversely, if �
Hence, �
belongs to �. �

� � �

�

�

�

� � � � � �

�

�

. Therefore, �

�

�

�

� �� in � we have �
, then, by (2.3), �
� �� does not belong to �, whence �

��

� �

� �

�

�

�

�

�

� � � � � �

.
.

�

�

�

� ��

� �

� � � � � ��

Theorems 2.75 and 2.76 correspond to analogous deﬁnability results in ﬁrst-order
logic: to get the analogous ﬁrst-order results, simply replace closure under bisim-
ulations in 2.75 and 2.76 by closure under isomorphisms; see the Notes at the end
of the chapter for further details. This close connection to ﬁrst-order logic may
explain why the results of this section seem to generalize to any modal logic that
has a standard translation into ﬁrst-order logic. For example, all of the results of
this section can also be obtained for basic temporal logic.

Exercises for Section 2.6
2.6.1 Prove Proposition 2.71: Let �
formulas � we have �
� iff �
such that �

��� � �, for all � � �.

� �

�

� be an ultrapower of �. Then, for all modal
is the constant function

�, where �

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

2.6.2 Give simple proofs of Theorem 2.75 and Theorem 2.76 using the analogous proof
for ﬁrst-order logic (see Theorem A.23).

2.6.3 Let � be an index set, and let �
such that for each � � �, �
of the two collections are bisimilar: �

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

.

be two collections of models
. Show that for any ultraﬁlter � over �, the ultraproducts

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

2.6.4

(a) Show that the ultraproduct of point-generated models need not be point-

generated.

(b) How is this for transitive models?

110

2 Models

2.7 Simulation and Safety

Theorem 2.68 provided a result characterizing the modal fragment of ﬁrst-order
logic as the class of formulas invariant for bisimulations. In this section we present
two further results in the same spirit; we focus on these results not just because they
are interesting and typical of current work in modal model theory, but also because
they provide instructive examples of how to apply the tools and proof strategies we
have discussed. We ﬁrst look at a notion of simulation that has been introduced
in various settings, and characterize the modal formulas preserved by simulations.
We then examine a question that arises in the setting of dynamic logic and process
algebra: which operations on models preserve bisimulation? That is, if we have
the back-and-forth clauses holding for �, and we apply an operation � to � which
returns a new relation ����, then when do we also have the back-and-forth-clauses
for ����?

Simulations

A simulation is simply a bisimulation from which half of the atomic clause and the
back clause have been omitted.

Deﬁnition 2.77 (Simulations) Let � be a modal similarity type. Let �

, � �

�

�

�

�

�

and �

�

�

�

�

� ��

� �

� �

�

�

�

�

�

� is called a � -simulation from � to �

� �� ,
be � -models. A non-empty binary relation
� if the following conditions

� � � � �

are satisﬁed.

(i) If �� �
(ii) If �� �

� and � � � ���, then �
� and �

� � � �

��

�

�

���.

� �

then there are �

�

, . . . , �

�

(in �

�) such that

�

�

�

�

�

�

�

� � � �

�

�

�

and for all � (� � � � �) �

�

� �

.

�

�

�

�

�

�

�

Thus, simulations only require that atomic information is preserved and that the
forth condition holds.

If � is a simulation from � in � to �
if there is a simulation � such that � �

� in �

�, we write � �

�;
�, we sometimes write

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

� �

�

�

�

�

� �

� �

�

�.

A modal formula � is preserved under simulations if for all models � and �
�,
�,

� in � and �

� implies �

� �

� �

�

�

�

�

and all states � and �
whenever it is the case that �

�, respectively, �
�. �

� �

�

�

� �

�

In various forms and under various names simulations have been considered in the-
oretical computer science. In the study of reﬁnement,� is interpreted as follows:
� reﬁnes or implements (the
if �
� �. And in the database world one looks at simulations the
system modeled by) �
other way around: if �

� then (the system modeled by) �

� constrains the structure of �

�, then �

� �

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

2.7 Simulation and Safety

111

�

�

�

� �

� then �

� itself. Note that
by only allowing those relational patterns that are present in �
� cannot enforce the presence of patterns. (See the
if �
Notes for references.) The following question naturally arises: which formulas
are preserved when passing from �
� along a simulation? Or, dually,
� � to �
which constraints on �

� � can be expressed by requiring that �

�?

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

�� � �� or �

Clearly simulations do not preserve the truth of all modal formulas. In particular,
let � be a one-point model with domain ��� and empty relation; then, there is a
� � to any state with the same valuation, no matter which model
simulation from �
it lives in. Using this observation it is easy to show that universal modal formulas of
�� � �� are not preserved under simulations. On the other hand,
the form �
�� � �� or
by clause (ii) of Deﬁnition 2.77 existential modal formulas of the form �
�� � �� are preserved under simulations. This leads to the conjecture that a modal
formula is preserved under simulations if, and only if, it is equivalent to a formula
that has been built from proposition letters, using only �, � and existential modal
operators, that is, diamonds or triangles. Below we will prove this conjecture; our
proof follows the proof of Theorem 2.68 to a large extent but there is an important
difference. Since we are working within a modal language, and not in ﬁrst-order
logic, we can make do with a detour via (m-saturated) ultraﬁlter extensions rather
than the (countably saturated) ultrapowers needed in the proof of Theorem 2.68.

Call a modal formula positive existential if it has been built up from proposition

letters, using only �, � and existential modal operators � and �.

Theorem 2.78 Let � be a modal similarity type, and let � be a � -formula. Then �
is preserved under simulations iff it is equivalent to a positive existential formula.

Proof. The easy inductive proof that positive existential formulas are preserved
under simulations is left to the reader. For the converse, assume that � is preserved
under simulations, and consider the set of positive existential consequences of �:

������ � �� � � is positive existential and � �� ���

We will show that ������ �� �; then, by compactness, � is equivalent to a positive
������; we need to show that
existential modal formula. Assume that �
��.

�. Let � � ��� � � is positive existential and �

� � �

� �

� �

�

�

�

�

Our ﬁrst claim is that the set ��� � � is consistent. For, suppose otherwise. Then
. By deﬁnition
. But

is a positive existential formula, hence, so is �

� � such that � �� �

, . . . , ��

� � � � � �

� � � � � �

�

�

�

�

there are formulas ��
each formula �
then �
for some � (� � � � �). This contradicts ��

� � � � � �

� �

�

�

�

�

�

�

�

, by assumption; from this it follows that �

� � .

� �

�

�

�

As a corollary we ﬁnd a model � and a state � of � such that �

� .
�.
Clearly, for every positive existential formula �, if �
It follows from Proposition 2.59 that for the ultraﬁlter extensions �� � and �� �

�, then �

� �

� �

� �

� �

�

�

�

�

�

112

2 Models

we have the same relation: for every positive existential formula �, if �� �
�, then �� �
�. By exploiting the fact that ultraﬁlter extensions are m-
saturated (Proposition 2.61), it can be shown that this relation is in fact a simulation
from �� �

; see Exercise 2.7.1.

to �� �

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

In a diagram we have now the following situation.

�

�

� �

� �

�

�

�

�

�

�

�� �

�� �

�

� �

� �

�

�

�

�

�

We can carry � around the diagram from �
implies �� �
we get �� �

� � to �
� by Proposition 2.59. Since � is preserved under simulations,
�. By Proposition 2.59 again we conclude �

� � as follows. �

�. �

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

Using Theorem 2.78 we can also answer the second of the two questions raised
above. Call a constraint � expressible if whenever �

� � satisﬁes � and �

�

� �

�

� �, then �

� � also satisﬁes �. By Theorem 2.78 the expressible constraints
(in ﬁrst-order logic) are precisely the ones that are (equivalent to) the standard
translations of negative universal modal formulas, that is, translations of modal
formulas built up from negated proposition letters using only �, � and universal
modal operators � and �.

Safety

Recall from Exercise 2.2.6 that bisimulations preserve the truth of formulas from
propositional dynamic logic. This result hinges on the fact that bisimulations not
corresponding to atomic programs, but also relations
only preserve the relations �
that are deﬁnable from these using PDL’s relational repertoire �, � and�. Put differ-
ently, if the back-and-forth conditions in the deﬁnition of a bisimulation hold for
�, . . . , then they also hold for any relation that is deﬁnable
the relations �
from these using �, � and �; these operations are ‘safe’ for bisimulation.

� , . . . , �

�

�

�

In this part of the section we work with modal similarity types having diamonds

only.

Deﬁnition 2.79 Let � be a modal similarity type, and let ���� �� denote an �
���-
formula with at most two free variables. Then ���� �� is called safe for bisimula-
tions if the following holds.

�

�

�

�

If � �
have �
then there is a state �

�� ���� ����� �,

�

� is a bisimulation with �� �

� and for some state � of � we

� of �

� such that �

�

�� ���� ����

�

�

�

� and �� �

�.

2.7 Simulation and Safety

113

In words, ���� �� is safe if the back-and-forth clauses hold for ���� �� whenever
they hold for the atomic relations. �

Example 2.80 (i) All PDL program constructors (�, �, and �) are safe for bisimu-
�, where � is a bisimulation, and ��� �� �
lations. For instance, assume that �� �
�� � � � in �. Then, there exists � with ��� and ��� in �; hence by the back-
� with �� �
and-forth conditions for � and �, we ﬁnd �
�, and a
� is the required �� � � �-successor of
�. Then �
� and �
state �

� with �� �

� and �

� in �

� in �

�

�

�

�

�

�

�

�

�

� in �
�.
(ii) Atomic tests �� ��, deﬁned by �� �� �� ���� �� � � � � � � ��, are safe. For,
�, where � is a bisimulation, and ��� �� � �� ��. Then � � � and
�� � ����. By the atomic clause in the deﬁnition of bisimulation, this implies

assume that �� �

�

�

�

�

�

�

� �

�� � ���

�. Hence, ��

� � �� ��, as required.
(iii) Dynamic negation ����, deﬁned by ���� � ���� �� � � � � � ��� ����,
�, where � is a bisimulation, and ��� �� � ���� in
� did have
�; then, by the back-and-forth conditions, � would have to

is safe. For, assume that �� �
�. Then, � � � and � has no �-successors in �. Now, suppose that �
an �
have an �-successor in � — a contradiction.

�-successor in �

(iv) Intersection of relations is not safe; see Exercise 2.7.2. �

Which operations are safe for bisimulations? Below, we give a complete answer for
the restricted case where we consider ﬁrst-order deﬁnable operations and languages
with diamonds only. We need some preparations before we can prove this result.

First, we deﬁne a modal formula � to be completely additive in a proposition

letter � if it satisﬁes the following.

For every family of non-empty sets ��
have ��� �

� � � � � � �� �

�

� iff, for some �, ��� �

�

such that � ��� �

�

�

�

�

� � � � � �

�� �

�

�

we
�, where

�

�

�

��� � �

and �

��� � � ��� for � �� �.

�

�

�

�

�

�

�

Completely additive formulas can be characterized syntactically. To this end, we
need the following technical lemma. Let � be a ﬁxed proposition letter. We write
� to denote the existence of a bisimulation for the modal language without the
proposition letter � (exactly which proposition letter is meant will be clear in the
applications of the lemma).

�

Lemma 2.81 Assume that � �
tive tree-like transition systems with �

� �

�

�

�

�

�

� �

�

� � � � ��

�

�

(� � � � �). Then there are extensions �

�

� �

�

�

�

, where � and � are intransi-
(in �), �
(in �) and
� of �

� � � � ��

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

� and �
�, and likewise

� �

�

of �

�

� �

�

� (i.e., the universe of � is a subset of the universe of �

114

2 Models

for � and �

�) such that

�

�

�

�

� �

� � �

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

�

�

�

�

�

� �

� �

�

�

� �

��

�

�

�

�

� is such that for any � (� � � � �) we have that �

and �

are only related

�

�

where �
to each other.

Proof. See Exercise 2.7.3. �

Lemma 2.82 A modal formula is completely additive in � iff it is equivalent to a
disjunction of path formulas, that is, formulas of the form

�

� ��

���

� � � � � ��

���

� �� � � ���

�

�

�

�

�

(2.4)

where � occurs in none of the formulas �

.

�

Proof. We only prove the hard direction. Assume that � is completely additive in
�. Deﬁne

������ ��

�� � � is of the form (2.4) and � �� ���

�

that is, ������ is an inﬁnite disjunction of modal formulas. We will show that
� �� ������; then, by compactness, � is equivalent to a ﬁnite disjunction of
formulas of the form speciﬁed in (2.4), and this proves the lemma.

�

�

� �

So, assume that �

�; we need to show �

������. It sufﬁces to
� and � �� �.
ﬁnd a formula � of the form speciﬁed in (2.4) such that �
By Lemma 2.15 we may assume that � is an intransitive, tree-like model with
. As � is completely additive in �, we may also assume that � ��� is just a
root �
; see Figure 2.8. Consider the following description of the above path
singleton �
leading up to �

:

� �

� �

�

�

�

�

�

�

�

� ��

� � � � � �

� � �

��� � � �

��

��

��

�

�

�

�

�

�

� and � � � � ��

� ��

�

�

� � � � � � � �� � �� �

��

�

�

�

��

�

�

�

��

where we use ��
The remainder of the proof is devoted to showing that � ��
and this will do to prove the lemma. For if � ��
some ﬁnite subset �

� to denote the set of � free modal formulas satisﬁed by �
.
���,
���, then, for

� we have �
is the only free variable in ��
���, this gives
���. It is easy to see that the latter formula is
(the standard translation of) a path formula �. Hence, we have found our formula
satisfying �

���, by compactness. Since �

� and � �� �.

� � � ��

� � � � � �

� � � � � �

� � � � � �

� � � � � �

� � � � � �

� � � � � �

� � � �

� ��

� ��

� ��

� ��

��

��

��

��

� �

��

��

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

2.7 Simulation and Safety

115

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

�
�

�
�

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

�
�
�

�
�
�

�

�

�

Fig. 2.8. True at only one state.

To show that � ��

� � � � � �

� ��

��

�

�

�

�� � ��

� with �
It follows from the deﬁnition of � that each �
formulas.

� � � � � �

� � � �

���

�

�

�

�

�

�

�

��� we proceed as follows. Take a model
�; we need to show that �
�.
agree on all � free modal
and �

�����

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

�

�

�

�

�

� �

� �

� �

�

� �

� �

� �

and �

and �

� and �

� and �

We may assume that � is an intransitive tree with root �. Take countably satu-
, respectively.
of �
rated elementary extensions �
� are elementary extensions of � and �, respectively, we may
Since �
� — things that can be ex-
assume a number of things about �
pressed by ﬁrst-order means, and hence are preserved under passing from a model
have no
to any of its elementary extensions. First, we may assume that �
incoming �-transitions, for any �, since this can be expressed by means of the
collection of all formulas of the form �� ����, where � is a binary relation sym-
bol in our language. Second, we may assume that states different from �
have at most one incoming �-transition, for any �, since this can be expressed by
the set of formulas of the form ���� ���� � ��� � � � � �. Summarizing, then,
and �
— but
� are actually

are very much like intransitive trees with roots �
� and �

possibly not quite: we have no guarantee that all nodes in �
accessible from �

, respectively, in ﬁnitely many steps.

and �

and �

and �

and �

� �

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

and �

agree on all modal formulas and Theorem 2.65,
Now, from the fact that �
. Next, we want to
we obtain a bisimulation �
apply Lemma 2.81, but to be able to do so, our models need to be rooted, intran-
� and
sitive trees. We can guarantee this by taking submodels �
, respectively. Clearly, for some �, we have

� that are generated by �

� such that �

�� and �

�� of �

and �

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

� �

�

�

�

��

�

��.

�

�

By Lemma 2.81 we can move to bisimilar extensions �
��, respectively, and ﬁnd a special bisimulation �

� linking �

�� and �
and �

�� of �

�� and
only to each

�

other (for � � � � �), as indicated in Figure 2.9.

�

�

We will amend the models �

�� and �

�� as follows. We shrink the interpretation

116

2 Models

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

�

�

�

��

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

�

�

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

�
�

�

�

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

��

��

��

�

�

�

�

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

�
�
�

�

�

�

�

�

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

Fig. 2.9. Linking �

only to �

(� � � � �).

�

�

of the proposition letter � so that it only holds at �
extend �

� to a full directed simulation �

�

�� for the whole language:

and �

. This allows us to

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

� �

� �

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

��

�

�

��

�

�

�

�

�

� �

� � �

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

��

�

�

�

��

�

�

�

�

�

� �

� �

�

�

� �

�

�

�

�

�

(2.5)

������

�

�

������

�

�

�

�

�

�

�

�

���

�

��

���

�

�

�

�

�

� �

� �

�

�

� �

��

�

�

�

�

We can chase � around the diagram displayed in (2.5), from �
Exercise 2.7.4. This proves the lemma. �

to �

� �

; see

� �

�

�

Lemma 2.83 For any program � and any formulas � and �, the following identi-
ties hold in any model:

(i) ����� � �����
(ii) �� � ��� � ���� � ����
(iii) ������� � ���� � �����.

The proof of this lemma is left as Exercise 2.7.5.

Theorem 2.84 Let � be a modal similarity type containing only diamonds, and let
���. Then ���� �� is safe for bisimulations
���� �� be a ﬁrst-order formula in �

�

�

2.7 Simulation and Safety

117

iff it can be deﬁned from atomic formulas �
�, � and �.

�

�� and atomic tests �� �� using only

Proof. To see that the constructions mentioned are indeed safe, consult Exam-
ple 2.80. Now, to prove the converse, let ���� �� be a safe ﬁrst-order operation, and
choose a new proposition letter �. Our ﬁrst observation is that �� ����� �� � � �� is
preserved under bisimulations. So by Theorem 2.68, the formula �� ����� ���� ��
is equivalent to a modal formula �.

Next we exploit special properties of � to arrive at our conclusion. First, because
of its special form, �� ����� �� � � �� is completely additive in � , and hence,
� is completely additive in �. Therefore, by Lemma 2.82 it is (equivalent to) a
disjunction of the form speciﬁed in (2.4). Then, ���� �� must be deﬁnable using
the corresponding union of relations ��
��. Finally, by
using Lemma 2.83 all complex tests can be pushed inside until we get a formula of
the required form, involving only �, �, � and �. �

�� � � � � � �

�� � �

� ��

� ��

�

�

�

�

�

Exercises for Section 2.7
2.7.1 Assume that � and �
existential formula � it holds that �
that �

�.

� �

� �

�

�

�

� are m-saturated models and suppose that for every positive
�. Prove

� for some � and �

� only if �

� �

� �

�

�

�

�

2.7.2 Prove that intersection of relations is not an operation that is safe for bisimulations
(see Example 2.80).

2.7.3 The aim of this exercise is to prove Lemma 2.81: assume that � �
where � and � are intransitive tree-like transition systems with �

�

�

�

�

�

� �

� � � �

�

�

�

�,
(in �),

� �

�

�

�

� � � �

�

�

�

�

(in �) and �

�

�

� �

(� � � � �).

�

�

�

(a) Explain why we may assume that all bisimulation links (between � and �) occur

between states at the same height in the tree.
(b) Next, work your way up along the branch �

bisimulation links involving the �
height 1, assume that �
� to �, connect �
by �
� � to �
link �
�) to � and that �

� �

�

�

�

�

�

� and �

� to the copy �

� �. Show that the resulting model �

� is bisimilar to � (in the sense of �

�).

�

�

�

�

�

�

� � � �

. from the �

and remove any double
. More precisely, and starting at
� �. Add a copy of the submodel generated
, and ‘divert’ the bisimulation
� of �
� is bisimilar (in the sense of

� by �

�

�

�

�

(c) Similar to the previous item, but now working up the branch �
to eliminate any double bisimulation links ending in one of the �

�

�

� � � �

�

�

�

�

in �

s (� � � � �).

�

(d) By putting together the previous items conclude that there are extensions �

�

�

�

� �

�

of �
verse of �

� and �
�, and likewise for � and �

� of �

� �

�

� �

� �

�

�

�

�

�

�

�) such that

� (i.e., the universe of � is a subset of the uni-

�

�

�

�

�

�

� �

� � �

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

�

�

�

�

�

�

�

� �

� �

�

�

� �

��

118

2 Models

where �
to each other.

� is such that for any � (� � � � �) we have that �

and �

are only related

�

�

2.7.4 Explain why we can chase � around the diagram displayed in (2.5) to infer �
from �

�.

� �

�

�

� �

�

�

�

2.7.5 Prove Lemma 2.83.

2.8 Summary of Chapter 2

� New Models from Old Ones: Taking disjoint unions, generated submodels, and
bounded morphic images are three important ways of building new models from
old that leave the truth values of modal formulas invariant.

� Bisimulations: Bisimulations offer a unifying perspective on model invariance,
and each of the constructions just mentioned is a kind of bisimulation. Bisimi-
larity implies modal equivalence, but the converse does not hold in general. On
image-ﬁnite models, however, bisimilarity and modal equivalence coincide.
� Using Bisimulations: Bisimulations can be used to establish non-deﬁnability
results (for example, to show that the global modality is not deﬁnable in the ba-
sic modal language), or to create models satisfying special relational properties
(for example, to show that every satisﬁable formula is satisﬁable in a tree-like
model).

� Finite Model Property: Modal languages have the ﬁnite model property (f.m.p.).
One technique for establishing the f.m.p. is by a selection of states argument
involving ﬁnite approximations to bisimulations. Another, the ﬁltration method,
works by collapsing as many states as possible.

� Standard Translation: The standard translation maps modal languages into clas-
sical languages (such as the language of ﬁrst-order logic) in a way that reﬂects
the satisfaction deﬁnition. Every modal formula is equivalent to a ﬁrst-order
formula in one free variable; if the similarity type is ﬁnite, ﬁnitely many vari-
ables sufﬁce to translate all modal formulas. Propositional dynamic logic has to
be mapped into a richer classical logic capable of expressing transitive closure.
� Ultraﬁlter Extensions: Ultraﬁlter extensions are built by using the ultraﬁlters
over a given model as the states of a new model, and deﬁning an appropriate re-
lation between them. This leads to the ﬁrst bisimilarity-somewhere-else result:
two states in two models are modally equivalent if and only if their (counterparts
in) the ultraﬁlter extensions of the two models are bisimilar.

� Van Benthem Characterization Theorem: The Detour Lemma — a bisimilarity-
somewhere-else result in terms of ultrapowers — can be used to prove the Van
Benthem Characterization Theorem: the modal fragment of ﬁrst-order logic is
the set of formulas in one free variable that are invariant for bisimulations.

2.8 Summary of Chapter 2

119

� Deﬁnability: The Detour Lemma also leads to the following result: the modally
deﬁnable classes of (pointed) models are those that are closed under bisimula-
tions and ultraproducts, while their complements are closed under ultrapowers.
� Simulation: The modal formulas preserved under simulations are precisely the

positive existential ones.

� Safety: An operation on relations is safe for bisimulations if whenever the back-
and-forth conditions hold for the base relations, they also hold for the result
of applying the operation to the relations. The ﬁrst-order operations safe for
bisimulations are the ones that can be deﬁned from atoms and atomic tests,
using only composition, union, and dynamic negation.

Notes

Kanger, Kripke, Hintikka, and others introduced models to modal logic in the late
1950s and early 1960s, and relational semantics (or Kripke semantics as it was
usually called) swiftly became the standard way of thinking about modal logic.
In spite of this, much of the material discussed in this chapter dates not from the
1960s, or even the 1970s, but from the late 1980s and 1990s. Why? Because re-
lational semantics was not initially regarded as of independent interest, rather it
was thought of as a tool that lead to interesting modal completeness theory and
decidability results. Only in the early 1970s (with the discovery of the frame in-
completeness results) did modal expressivity become an active topic of research
— and even then, such investigations were initially conﬁned to expressivity at the
level of frames rather than at the level of models. Thus the most fundamental level
of modal semantics was actually the last to be explored mathematically.

Generated submodels and bounded morphisms arose as tools for manipulating
the canonical models used in modal completeness theory (we discuss canonical
models in Chapter 4). Point-generated submodels, however, were already men-
tioned, under the name of connected model structures, in Kripke [291]. Bounded
morphisms go back to at least Segerberg [396], where they are called pseudo epi-
morphisms; this soon got shortened down to p-morphism, which remains the most
widely used terminology. A very similar, earlier, notion is in de Jongh and Troel-
stra [103]. The name bounded morphism stems from Goldblatt [192]. Disjoint
unions and ultraﬁlter extensions seem to have ﬁrst been isolated when modal lo-
gicians started investigating modal expressivity over frames in the 1970s (along
with generated submodels and bounded morphisms they are the four constructions
needed in the Goldblatt-Thomason theorem, which we discuss in the following
chapter). Neither construction is as useful as generated submodels and bounded
morphisms when it comes to proving completeness results, which is probably why
they weren’t noted earlier. However, both arise naturally in the context of modal
duality theory, cf. Goldblatt [190, 191]. Ultraﬁlter extensions independently came

120

2 Models

about in the model-theoretic analysis of modal logic, see Fine [140]; the name
seems to be due to van Benthem. The unraveling construction (that is, unwind-
ing arbitrary models into trees; see Proposition 2.15) is helpful in many situations.
Surprisingly, it was ﬁrst used as early as in 1959, by Dummett and Lemmon [125],
but the method only seems to have become widely known because of Sahlqvist’s
heavy use of it in his classic 1975 paper [388].

Vardi [434] has stressed the importance of the tree model property of modal
logic: the property that a formula is satisﬁable iff it is satisﬁable at the root of a
tree-like model. The tree model property paves the way for the use of automata-
theoretic tools and tableaux-based proof methods. Moreover, it is essential for
explaining the so-called robust decidability of modal logic — the phenomenon
that the basic modal logic is decidable itself, and of reasonably low complexity,
and that these features are preserved when the basic modal logic is extended by a
variety of additional constructions, including counting, transitive closure, and least
ﬁxed points.

We discussed two ways of building ﬁnite models:

the selection method and
ﬁltration. However, the use of ﬁnite algebras predates the use of ﬁnite models:
they were ﬁrst used in 1941 by McKinsey [328]; Lemmon [302] used and extended
this method in 1966. The use of model-theoretic ﬁltration dates back to Lemmon
and Scott’s long unpublished monograph Intensional Logic [303] (which began
circulating in the mid 1960s); it was further developed in Segerberg’s An Essay in
Classical Modal Logic [396], which also seems to have given the method its name
(see also Segerberg [394]). We introduced the selection method via the notion of
ﬁnitely approximating a bisimulation, an idea which seems to have ﬁrst appeared
in 1985 in Hennessy and Milner [225].

The standard translation, in various forms, can be found in the work of a number
of writers on modal and tense logic in the 1960s — but its importance only became
fully apparent when the ﬁrst frame incompleteness results were proved. Thoma-
son [426], the paper in which frame incompleteness results was ﬁrst established,
uses the standard translation — and shows why the move to frames and validities
requires a second-order perspective (something we will discuss in the following
chapter). Thus the need became clear for a thorough investigation of the relation
between modal and classical logic, and correspondence theory was born. But al-
though other authors (notably Sahlqvist [388]) helped pioneer correspondence the-
ory, it was the work of Van Benthem [35] which made clear the importance of sys-
tematic use of the standard translation to access results and techniques from classi-
cal modal theory. The observation that at most two variables are needed to translate
basic modal formulas into ﬁrst-order logic is due to Gabbay [158]. The earliest
systematic study of ﬁnite variable fragments seems to be due to Henkin [223] in
the setting of algebraic logic, and Immerman and Kozen [246] study the link with
complexity and database theory. Consult Otto [355] for more on ﬁnite variable

2.8 Summary of Chapter 2

121

logics. Keisler [272] is still a valuable reference for inﬁnitary logic. A variety of
other translations from modal to classical logic have been studied, and for a wide
variety of purposes. For example, simply standardly translating modal logics into
ﬁrst-order logic and then feeding the result to a theorem prover is not an efﬁcient
way of automating modal theorem proving. But the idea of automating modal rea-
soning via translation is interesting, and a variety of translations more suitable for
this purpose have been devised; see Ohlbach et al. [351] for a survey.

Under the name of p-relations, bisimulations were introduced by Johan van Ben-
them in the course of his work on correspondence theory. Key references here are
Van Benthem’s 1976 PhD thesis [35]; his 1983 book based on the thesis [35]; and
[42], his 1984 survey article on correspondence theory. In keeping with the spirit
of the times, most of Van Benthem’s early work on correspondence theory dealt
with frame deﬁnability (in fact he devotes only 6 of the 227 pages in his book
to expressivity over models). Nonetheless, much of this chapter has its roots in
this early work, for in his thesis Van Benthem introduced the concept of a bisim-
ulation (he used the name p-relation in [35, 41], and the name zigzag relation in
[42]) and proved the Characterization Theorem. His original proof differs from
the one given in the text: instead of appealing to saturated models, he employs an
elementary chains argument. Explicitly isolating the Detour Lemma (which brings
out the importance of ultrapowers) opens the way to Theorems 2.75 and 2.76 on
deﬁnability and makes explicit the interesting analogies with ﬁrst-order model the-
ory discussed below. On the other hand, the original proof is more concrete. Both
are worth knowing. The ﬁrst published proof using saturated models seems to be
due to Rodenburg [382], who used it to characterize the ﬁrst-order fragment corre-
sponding to intuitionistic logic.

The back-and-forth clauses of a bisimulation can be adapted to analyze the ex-
pressivity of a wide range of extended modal logics (such as those studied in Chap-
ter 7), and such analyses are now commonplace. Bisimulation based characteriza-
tions have been given for the modal mu-calculus by Janin and Walukiewicz [249],
for temporal logics with since and until by Kurtonina and De Rijke [295], for
subboolean fragments of knowledge representation languages by Kurtonina and
De Rijke [296], and for CTL� by Moller and Rabinovich [339]. Related model-
theoretic characterizations can be found in Immerman and Kozen [246] (for ﬁnite
variable logics) and Toman and Niwi´nski [430] (for temporal query languages).
Rosen [384] presents a version of the Characterization Theorem that also works
for the case of ﬁnite models; the proof given in the text breaks down in the ﬁnite
case as it relies on compactness and saturated models.

But bisimulations did not just arise in modal logic — they were independently
invented in computer science as an equivalence relation on process graphs. Park
[358] seems to have been the ﬁrst author to have used bisimulations in this way.
The classic paper on the subject is Hennessy and Milner [225], the key reference for

122

2 Models

the Hennessy-Milner Theorem. The reader should be warned, however, that just as
the notion of bisimulation can be adapted to cover many different modal systems,
the notion of bisimulation can be adapted to cover many different concepts of pro-
cess — in fact, a survey of bisimulation in process algebra in the early 1990s lists
over 155 variants of the notion [179]! Our deﬁnitions do not exclude bisimulations
between a model and itself (auto-bisimulations); the quotient of a model with re-
spect to its largest auto-bisimulation can be regarded as a minimal representation
of this model. The standard method for computing the largest auto-bisimulation is
the so-called Paige-Tarjan algorithm; see the contributions to Ponse, de Rijke and
Venema [364] for relevant pointers and surveys.

More recently, bisimulations have become fundamental in a third area, non-well
founded set theory. In such theories, the axiom of foundation is dropped, and sets
are allowed to be members of themselves. Sets are thought of as graphs, and two
sets are considered identical if and only if they are bisimilar. The classic source for
this approach is Aczel [2], who explicitly draws on ideas from process theory. A
recent text on the subject is Barwise and Moss [26], who link their work with the
modal tradition. For recent work on modal logic and non-well founded set theory,
see Baltag [19].

�

The name ‘m-saturation’ stems from Visser [443], but the notion is older: its ﬁrst
occurrence in the literature seems to be in Fine [140] (under the name ‘modally
’). The concept of a Hennessy-Milner class is from Goldblatt [185] and
saturated
Hollenberg [239]. Theorem 2.62, that equivalence of models implies bisimilar-
ity between their ultraﬁlter extensions, is due to [239]. Chang and Keisler [89,
Chapters 4 and 6] is the classic reference for the ultraproduct construction; their
Chapters 2 and 5 also contain valuable material on saturated models. Doets and
Van Benthem [120] give an intuitive explanation of the ultraproduct construction.

The results proved in this chapter are often analogs of standard results in ﬁrst-
order model theory, with bisimulations replacing partial isomorphisms. The Keis-
ler-Shelah Theorem (see Chang and Keisler [89, Theorem 6.1.15]) states that two
models are elementarily equivalent iff they have isomorphic ultrapowers; a weak-
ened form, due to Doets and Van Benthem [120], replaces ‘isomorphic’ with ‘par-
tially isomorphic’. Theorem 2.74, which is due to De Rijke [109], is a modal ana-
log of this weakened characterization theorem. Proposition 2.31 is similar to char-
acterizations of logical equivalence for ﬁrst-order logic due to Ehrenfeucht [127]
and Fra¨ıss´e [149]; in fact, bisimulations can be regarded as the modal cousins of the
model theoretic Ehrenfeucht-Fra¨ıss´e games. We will return to the theme of analo-
gies between ﬁrst-order and modal model theory in Section 7.6 when we prove a
Lindstr¨om theorem for modal logic. See De Rijke [109] and Sturm [418] for further
work on modal model theory; De Rijke and Sturm [113] provide global counter-
parts for the local deﬁnability results presented in Section 2.6. One can also charac-

2.8 Summary of Chapter 2

123

terize modal deﬁnability of model classes using ‘modal’ structural operations only,
i.e., bisimulations, disjoint unions and ultraﬁlter extensions, cf. Venema [437].

Sources for the use of simulations in reﬁnement are Henzinger et al. [227] and
He Jifeng [252], and for their use in a database setting, consult Buneman et al. [74];
see De Rijke [106] for Theorem 2.78. The Safety Theorem 2.84 is due to Van
Benthem [47]. The text follows the original proof fairly closely; an alternative
proof has been given by Hollenberg [238], who also proves generalizations.

One ﬁnal remark. Given the importance of ﬁnite model theory, the reader may
be surprised to ﬁnd so little in this chapter on the topic. But we don’t neglect
ﬁnite model theory in this book: virtually all the results proved in Chapter 6 re-
volve around ﬁnite models and the way they are structured. That said, the topic
of ﬁnite modal model theory has received less attention from modal logicians than
it deserves. In spite of Rosen’s [384] proof of the Van Benthem characterization
theorem for ﬁnite models, and in spite of work on modal 0-1 laws (Halpern and
Kapron [211], Goranko and Kapron [197], and Grove et al. [206, 205]), ﬁnite
modal model theory is clearly an area where interesting questions abound.


