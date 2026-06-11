4

Completeness

This chapter is about the completeness — and incompleteness — of normal modal
logics. As we saw in Section 1.6, normal modal logics are collections of formulas
satisfying certain simple closure conditions. They can be speciﬁed either syntac-
tically or semantically, and this gives rise to the questions which dominate the
chapter: Given a semantically speciﬁed logic, can we give it a syntactic characteri-
zation, and if so, how? And: Given a syntactically speciﬁed logic, can we give it a
semantic characterization (and in particular, a characterization in terms of frames),
and if so, how? To answer either type of question we need to know how to prove
(soundness and) completeness theorems, and the bulk of the chapter is devoted to
developing techniques for doing so.

The chapter has two major parts. The ﬁrst, comprising the ﬁrst four sections,
is an introduction to basic completeness theory. It introduces canonical models,
explains and applies the completeness-via-canonicity proof technique, discusses
the Sahlqvist Completeness Theorem, and proves two fundamental limitative re-
sults. The material introduced in these sections (which are all on the basic track) is
needed to follow the second part and the algebraic investigations of Chapter 5.

In the second part of the chapter we turn to the following question: what are we
to do when canonicity fails? (As will become clear, canonicity failure is a fact of
life for temporal logic, propositional dynamic logic, and other applied modal lan-
guages.) This part of the chapter is technique oriented: it introduces ﬁve important
ways of dealing with such difﬁculties.

Chapter guide

Section 4.1: Preliminaries (Basic track). This section introduces the fundamental

concepts: normal modal logics, soundness, and completeness.

Section 4.2: Canonical Models (Basic track). Canonical models are introduced,

and the fundamental Canonical Model Theorem is proved.

Section 4.3: Applications (Basic track). This section discusses the key concept of

190

4.1 Preliminaries

191

canonicity, and uses completeness-via-canonicity arguments to put canoni-
cal models to work. We prove completeness results for a number of modal
and temporal logics, and ﬁnish with a discussion of the Sahlqvist Com-
pleteness Theorem.

Section 4.4: Limitative Results (Basic track). We prove two fundamental limita-
tive results: not all normal logics are canonical, and not all normal logics
are characterized by some class of frames. This section concludes our in-
troduction to basic completeness theory.

Section 4.5: Transforming the Canonical Model (Basic track). Often we need to
build models with properties for which we lack a canonical formula. What
are we to do in such cases? This section introduces one approach: use
transformation methods to try and massage the ‘faulty’ canonical model
into the required shape.

Section 4.6: Step-by-Step (Basic track). Sometimes we can cope with canonicity
failure using the step-by-step method. This is a technique for building
models with special properties inductively.

Section 4.7: Rules for the Undeﬁnable (Basic track). Special proof rules (that in
a certain sense manage to express undeﬁnable properties of models and
frames) sometimes allow us to construct special canonical models con-
taining submodels with undeﬁnable properties.

Section 4.8: Finitary Methods I (Basic track). We discuss a method for proving
weak completeness results for non-compact logics: ﬁnite canonical mod-
els. We use such models to prove the completeness of propositional dy-
namic logic.

Section 4.9: Finitary Methods II (Advanced track). This section further explores
ﬁnitary methods, this time the direct use of ﬁltrations. We illustrate this
with an analysis of the normal logics extending S4.3.

4.1 Preliminaries

In this section we introduce some of the fundamental concepts that we will use
throughout the chapter. We begin by deﬁning modal logics — these could be de-
scribed as propositional logics in a modal language.

Throughout the chapter we assume we are working with a ﬁxed countable lan-

guage of proposition letters.

Deﬁnition 4.1 (Modal Logics) A modal logic � is a set of modal formulas that
contains all propositional tautologies and is closed under modus ponens (that is, if
�) and uniform substitution (that is, if � belongs
� we say that � is a theorem
are modal logics such

� then �
to � then so do all of its substitution instances). If �
of � and write �

�; if not, we write ��

� and �

�. If �

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

192

4 Completeness

that �
drop the word ‘modal’ and talk simply of ‘logics’. �

is an extension of �

, we say that �

�

�

�

�

�

�

. In what follows, we usually

Note that modal logics contain all substitution instances of the propositional tau-
tologies: for example, �
�, belongs to every modal logic. Even though
such substitution instances may contain occurrences of � and �, we still call them
tautologies. Clearly tautologies are valid in every class of models.

� �

�

�

Example 4.2
logic.

(i) The collection of all formulas is a logic, the inconsistent

(ii) If �
(iii) Deﬁne �S to be �

�

�

�

�

�

�

� is a collection of logics, then

is a logic.

�

�

�

�

�

�

�

�

�

�� for all structures �

� where � is any
class of frames or any class of general frames. �S is a logic. If S is the
singleton class �

�, we usually call this logic �
(iv) If � is a class of models, then �M need not be a logic. Consider a model
�.

� in which � is true at all nodes but � is not. Then �
But � is obtainable from � by uniform substitution. �

�, rather than �

�, but �

.

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

It follows from Examples 4.2(i) and 4.2(ii) that there is a smallest logic containing
any set of formulas � ; we call this the logic generated by � . For example, the logic
generated by the empty set contains all the tautologies and nothing else; we call it
PC and it is a subset of every logic. This generative perspective is essentially syn-
tactic. However, as Example 4.2(iii) shows, there is a natural semantic perspective
on logics: both frames and general frames give rise to logics in an obvious way.
Even the empty class of frames gives rise to a logic, namely the inconsistent logic.
Finally, Example 4.2(iv) shows that models may fail to give rise to logics. This
‘failure’ is actually the behavior we should expect: as we discussed in Section 1.6,
genuine logics arise at the level of frames, via the concept of validity.

Deﬁnition 4.3 Let �
in propositional calculus from assumptions �
a tautology. �

, . . . , �

�

�

, � be modal formulas. We say that � is deducible
� is
if �

, . . . , �

� � � � �

� �

�

�

�

�

�

�

All logics are closed under deduction in propositional calculus: if � is deducible
in propositional calculus from assumptions �
implies �

, then �

, . . . , �

, . . . , �

�.

�

�

�

�

�

�

�

�

�

Deﬁnition 4.4 If �
� is �-deducible from � ) if �

� �

�

� is a set of formulas then � is deducible in � from � (or:

� or there are formulas �

,. . . , �

� such that

�

�

�

�

�

�

� � � � �

� �

�

�

��

�

�

�

4.1 Preliminaries

193

If this is the case we write �
consistent if �

�. A set of formulas � is �-
�, and �-inconsistent otherwise. A formula � is �-consistent if

�, if not, �

��

��

�

�

�

� is; otherwise it is �-inconsistent. �

�

�

�

It is a simple exercise in propositional logic to check that a set of formulas � is
�-inconsistent if and only if there is a formula � such that �
� if and
only if for all formulas �, �
�. Moreover, � is �-consistent if and only if
every ﬁnite subset of � is. (That is, our notion of deducibility has the compact-
ness property.) From now on, when � is clear from context or irrelevant, we drop
explicit references to it and talk simply of ‘theorems’, ‘deducibility’, ‘consistency’
and ‘inconsistency’, and use the notation �

�, and so on.

�, �

� �

�

�

�

�

�

�

The preceding deﬁnitions merely generalize basic ideas of propositional calculus
to modal languages. Now we come to a genuinely modal concept: normal modal
logics. These logics are the focus of this chapter’s investigations. We initially
restrict our discussion to the basic modal language; the full deﬁnition is given at
the end of the section. As we discussed in Section 1.6, the following deﬁnition is
essentially an abstraction from Hilbert-style approaches to modal proof theory.

Deﬁnition 4.5 A modal logic � is normal if it contains the formulas:

(K)
(Dual) �

�

�

� �

�

�

�,

�

�

�

�

�

� � �

�

�

�

�,

�

and is closed under generalization (that is, if �

� then �

�). �

�

�

�

Syntactic issues do not play a large role in this book; nonetheless, readers new to
modal logic should study the following lemma and attempt Exercise 4.1.2.

Lemma 4.6 For any normal logic �, if �

�

� then �

�

�

�

�

�

�

�

�.

Proof. Suppose �

�. Then �

� and �

�

�

�

�

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

�

�

�

�

�

�

�, the desired result follows. Now, as �

�

�, hence by generalization �

�

�

�

� �

we have �
substitution into the K axiom we obtain �
follows by modus ponens that �
and two uses of Dual yield �
argument shows that �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�, as desired. As �
�, and the result follows. �

�

��

�

�

�

��

� �

�

�

�

� � �

�. Therefore, �

�

�

�

�

�

� �

�. If we can show that
�,
�. By uniform
�. It
�,
�, an analogous

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

Remark 4.7 The above deﬁnition of normal logics (with or without Dual, depend-
ing on the choice of primitive operators) is probably the most popular way of stip-
ulating what normal logics are. But it’s not the only way. Here, for example, is
a simple diamond-based formulation of the concept, which will be useful in our
� � � and
later algebraic work: a logic � is normal if it contains the axioms �
� implies

�, and is closed under the following rule: �

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

194

4 Completeness

�

�

�

�

�

�. This formulation is equivalent to Deﬁnition 4.5, as the reader is

�

asked to show in Exercise 4.1.2. �

Example 4.8

(i) The inconsistent logic is a normal logic.

(ii) PC is not a normal logic.
(iii) If �

�

�

�

�

�

� is a collection of normal logics, then

�

logic.

is a normal

�

�

�

�

�

(iv) If � is any class of frames, then �F is a normal logic.
(v) If � is any class of general frames, then �G is a normal logic. (The reader

�

is asked to prove this in Exercise 4.1.1.) �

�

�.

Examples 4.8(i) and 4.8(iii) guarantee that there is a smallest normal modal logic
containing any set of formulas � . We call this the normal modal logic generated
or axiomatized by � . The normal modal logic generated by the empty set is called
�, and it is the smallest (or minimal) normal modal logic: for any normal modal
If � is a non-empty set of formulas we usually denote the
logic �, �
normal logic generated by � by ��. Moreover, we often make use of Hilbert
axiomatization terminology, referring to � as axioms of this logic, and say that the
logic was generated using the rules of proof modus ponens, uniform substitution,
and generalization. We justiﬁed this terminology in Section 1.6, and also asked the
reader to prove that the logic �� consists of precisely those formulas that can be
proved in a Hilbert-style derivation from the axioms in � using the standard modal
proof rules (see Exercise 1.6.6).

Deﬁning a logic by stating which formulas generate it (that is, extending the
minimal normal logic � with certain axioms of interest) is the usual way of syn-
tactically specifying normal logics. Much of this chapter explores such axiomatic
extensions. Here are some of the better known axioms, together with their tradi-
tional names:

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

(4) ��
(T)
(B)
(D) �
(.3) �
(L) �

�

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

�

�

�

�

�

are axioms then KA

There is a convention for talking about the logics generated by such axioms: if
, . . . ,
� � � � � A
A
. But irregularities abound. Many historical names are ﬁrmly entrenched, thus
A
modal logicians talk of T, S4, B, and S5 instead of KT, KT4, KB and KT4B re-
spectively. Moreover, many axioms have multiple names. For example, the axiom
we call L (for L¨ob) is also known as G (for G¨odel) and W (for wellfounded); and

is the normal logic generated by A

� � � A�

�

�

�

4.1 Preliminaries

195

K
K4
T
B
KD
S4
S5
K4.3
S4.3
KL

the class of all frames
the class of transitive frames
the class of reﬂexive frames
the class of symmetric frames
the class of right-unbounded frames
the class of reﬂexive, transitive frames
the class of frames whose relation is an equivalence relation
the class of transitive frames with no branching to the right
the class of reﬂexive, transitive frames with no branching to the right
the class of ﬁnite transitive trees (weak completeness only)

Table 4.1. Some Soundness and Completeness Results

the axiom we call .3 has also been called H (for Hintikka). We adopt a fairly relaxed
attitude towards naming logics, and use the familiar names as much as possible.

Now that we know what normal modal logics are, we are ready to introduce the
two fundamental concepts linking the syntactic and semantic perspectives: sound-
ness and completeness.

Deﬁnition 4.9 (Soundness) Let � be a class of frames (or models, or general
frames). A normal modal logic � is sound with respect to � if �
�. (Equiva-
lently: � is sound with respect to � if for all formulas �, and all structures �
�,
�.) If � is sound with respect to � we say that � is a class of

� implies �

�

�

�

�

�

�

frames (or models, or general frames) for �. �

Table 4.1 lists a number of well-known logics together with classes of frames for
which they are sound. Recall that a right-unboundedness frame �
� is a frame
such that �

� ���. Also, a frame �

� satisfying �

�� �

�� �

���

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

�

�

�

�

���

���

�� is said to have no branching to the right.
The soundness claims made in Table 4.1 (with the exception of the last one,
which was shown in Example 3.9) are easily demonstrated. In all cases one shows
that the axioms are valid, and that the three rules of proof (modus ponens, gen-
eralization, and uniform substitution) preserve validity on the class of frames in
question. In fact, the proof rules preserve validity on any class of frames or general
frames (see Exercise 4.1.1), so proving soundness boils down to checking the va-
lidity of the axioms. Soundness proofs are often routine, and when this is the case
we rarely bother to explicitly state or prove them. But the concept of completeness,
leads to the problems that will occupy us for the remainder of the chapter.

Deﬁnition 4.10 (Completeness) Let � be a class of frames (or models, or general
frames). A logic � is strongly complete with respect to � if for any set of formulas

196

�

�, if �

� �

�

4 Completeness

�S � then �

�

�

�. That is, if � semantically entails � on S (recall

Deﬁnition 1.35) then � is �-deducible from � .

A logic � is weakly complete with respect to � if for any formula �, if � �

� then
�. � is strongly complete (weakly complete) with respect to a single structure

�

�

� if � is strongly complete (weakly complete) with respect to �

�

�. �

Note that weak completeness is the special case of strong completeness in which �
is empty, thus strong completeness with respect to some class of structures implies
weak completeness with respect to that same class. (The converse does not hold,
as we will later see.) Note that the deﬁnition of weak completeness can be refor-
mulated to parallel the deﬁnition of soundness: � is weakly complete with respect
�. Thus, if we prove that a syntactically speciﬁed logic � is both
to � if �S �
sound and weakly complete with respect to some class of structures �, we have
established a perfect match between the syntactical and semantical perspectives:
� (that is, the logic of some class
of structures � of interest) we often want to ﬁnd a simple collection of formulas �
such that �
� is the logic generated by � ; in such a case we sometimes say that �
axiomatizes �.

�S. Given a semantically speciﬁed logic �

�

�

Example 4.11 With the exception of KL, all the logics mentioned in Table 4.1 are
strongly complete with respect to the corresponding classes of frames. However
KL is only weakly complete with respect to the class of ﬁnite transitive trees. As
we will learn in section 4.4, KL is not strongly complete with respect to this class
of frames, or indeed with respect to any class of frames whatsoever. �

These completeness results are among the best known in modal logic, and we will
soon be able to prove them. Together with their soundness counterparts (given in
Example 4.1), they constitute perspicuous semantic characterizations of important
logics. K4, for example, is not just the logic obtained by enriching K with some
particular axiom: it is precisely the set of formulas valid on all transitive frames.
There is always something arbitrary about syntactic presentations; it is pleasant
(and useful) to have these semantic characterizations at our disposal.

We make heavy use, usually without explicit comment, of the following result.

Proposition 4.12 A logic � is strongly complete with respect to a class of struc-
tures � iff every �-consistent set of formulas is satisﬁable on some �
�. �
is weakly complete with respect to a class of structures � iff every �-consistent
formula is satisﬁable on some �

�.

�

�

Proof. The result for weak completeness follows from the one for strong complete-
ness, so we examine only the latter. To prove the right to left implication we argue
by contraposition. Suppose � is not strongly complete with respect to �. Thus

4.1 Preliminaries

197

there is a set of formulas �
is �-consistent, but not satisﬁable on any structure in �. The left to right direction
is left to the reader. �

� such that �

�. Then �

� but �

� ��

� �

�

��

�

�

�

�

�

To conclude this section, we extend the deﬁnition of normal modal logics to arbi-
trary similarity types.

Deﬁnition 4.13 Assume we are working with a modal language of similarity type
� . A modal logic in this language is (as before) a set of formulas containing all
tautologies that is closed under modus ponens and uniform substitution. A modal
logic � is normal if for every operator � it contains: the axiom �
� (for all � such
��; the axiom Dual�; and is closed under the generalization rules
that � �
described below.

�

�

�

�

�

�

The required axioms are obvious polyadic analogs of the earlier K and Dual

axioms:

(K�

�)

�

�

�

� �

�

� � � � � �

� � � � � � �

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

� � � � � �� � � � � �

�

�

� � � � � � � � � � � �

�

�

�

�

�

�

�

�

�

�

�

�

�

(Dual�) �

�

� � �

��

�

�

� � � � � �

�

�

� � � � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

are distinct propositional variables, and the occurrences
� of � and � occur in the �-th argument place of �.) Finally, for a polyadic

(Here �� � � �
K�
operator �, generalization takes the following form:

� � � � � �

�

�

�

�

�

� implies �

�

�

�

�

��

��

� � � � � �� � � � �

�

That is, an �-place operator � is associated with � generalization rules, one for
each of its � argument positions.

Note that these axioms and rules don’t apply to nullary modalities. Nullary
modalities are rather like propositional variables and — as far as the minimal logic
is concerned — they don’t give rise to any axioms or rules. �

Deﬁnition 4.14 Let � be a modal similarity type. Given a set of � -formulas � ,
� , the normal modal logic axiomatized or generated by � , to be the
we deﬁne �
smallest normal modal � -logic containing all formulas in � . Formulas in � are
called axioms of this logic, and � may be called an axiomatization of �
� . The
normal modal logic generated by the empty set is denoted by �

. �

�

�

�

Exercises for Section 4.1
4.1.1 Show that if � is any class of general frames, then �
� is a normal logic. (To prove
this, you will have to show that the modal proof rules preserve validity on any general
frame.)

198

4 Completeness

4.1.2 First, show that the diamond-based deﬁnition of normal modal logics given in Re-
mark 4.7 is equivalent to the box-based deﬁnition. Then, for languages of arbitrary simi-
larity type, formulate a �-based deﬁnition of normal modal logics, and prove it equivalent
to the �-based one given in Deﬁnition 4.13.

4.1.3 Show that the set of all normal modal logics (in some ﬁxed language) ordered by set
theoretic inclusion forms a complete lattice. That is, prove that every family �
of logics has both an inﬁmum and a supremum. (An inﬁmum is a logic � such that �
for all �
supremum is deﬁned analogously, with ‘�’ replacing ‘�’.)

�, and for any other logic �

� that has this property, �

�; the concept of a

�

�

�

�

�

�

�

�

�

�

�

�

�

4.1.4 Show that the normal logic generated by �
� is sound
with respect to the class of K4.3 frames (see Table 4.1). Further, show that the normal
� is not sound with respect to this class
modal logic generated by �
of frames, but that it is sound with respect to the class of S4.3 frames.

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

�

�

�

4.2 Canonical Models

Completeness theorems are essentially model existence theorems — that is the con-
tent of Proposition 4.12. Given a normal logic �, we prove its strong completeness
with respect to some class of structures by showing that every �-consistent set of
formulas can be satisﬁed in some suitable model. Thus the fundamental question
we need to address is: how do we build (suitable) satisfying models?

This section introduces the single most important answer: build models out of
maximal consistent sets of formulas, and in particular, build canonical models. It
is difﬁcult to overstress the importance of this idea.
In one form or another it
underlies almost every modal completeness result the reader is likely to encounter.
Moreover, as we will learn in Chapter 5, the idea has substantial algebraic content.

Deﬁnition 4.15 (�-MCSs) A set of formulas � is maximal �-consistent if � is �-
consistent, and any set of formulas properly containing � is �-inconsistent. If � is
a maximal �-consistent set of formulas then we say it is a �-MCS. �

�

�

�

�

�

� �

�.

Why use MCSs in completeness proofs? To see this, ﬁrst note that every point
� in every model � for a logic � is associated with a set of formulas, namely
It is easy to check (and the reader should do so) that this
set of formulas is actually a �-MCS. That is: if � is true in some model for �,
then � belongs to a �-MCS. Second, if � is related to �
� in some model �,
then it is clear that the information embodied in the MCSs associated with � and
� is ‘coherently related’. Thus our second observation is: models give rise to

�

�

collections of coherently related MCSs.

The idea behind the canonical model construction is to try and turn these obser-
vations around: that is, to work backwards from collections of coherently related
MCSs to the desired model. The goal is to prove a Truth Lemma which tells us that

4.2 Canonical Models

199

‘� belongs to an MCS’ is actually equivalent to ‘� is true in some model’. How
will we do this? By building a special model — the canonical model — whose
points are all MCSs of the logic of interest. We will pin down what it means for
the information in MCSs to be ‘coherently related’, and use this notion to deﬁne
the required accessibility relations. Crucially, we will be able to prove an Exis-
tence Lemma which states that there are enough coherently related MCSs to ensure
the success of the construction, and this will enable us to prove the desired Truth
Lemma.

To carry out this plan, we need to learn a little more about MCSs.

Proposition 4.16 (Properties of MCSs) If � is a logic and � is a �-MCS then:

� ;

(i) � is closed under modus ponens: if �, �
(ii) �
(iii) for all formulas �: �
(iv) for all formulas �, �: �

� ;
� iff �

� or �

�

�

�

�

�

�

�

�

�

�

�

� , then �

� ;

�

� or �

� .

�

Proof. Exercise 4.2.1. �

As MCSs are to be our building blocks, it is vital that we have enough of them. In
fact, any consistent set of formulas can be extended to a maximal consistent one.

Lemma 4.17 (Lindenbaum’s Lemma) If � is a �-consistent set of formulas then
�.
there is an �-MCS

� such that �

�

�

�

Proof. Let �
, �
deﬁne the set �

�

, �

� � � � be an enumeration of the formulas of our language. We

�

�

� as the union of a chain of �-consistent sets as follows:

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

if this is �-consistent

�

�

�

��

�

�

�

�

�

� ��

� otherwise

�

�

�

�

�

�

�

�

��

The proof of the following properties of �
�-consistent, for all �; (ii) exactly one of � and �
�; and ﬁnally (iv) �
(iii) if �

�, then �

�

�

�

�

�

� is left as Exercise 4.2.2: (i) �

is
�, for every formula �;

�

� is in �
� is a �-MCS. �

�

We are now ready to build models out of MCSs, and in particular, to build the
very special models known as canonical models. With the help of these structures
we will be able to prove the Canonical Model Theorem, a universal completeness
result for normal logics. We ﬁrst deﬁne canonical models and prove this result for
the basic modal language; at the end of the section we generalize our discussion to
languages of arbitrary similarity type.

200

4 Completeness

Deﬁnition 4.18 The canonical model �
language) is the triple �

� �

� �

�

�

�

�

� where:

� for a normal modal logic � (in the basic

(i) �
(ii) �

� is the set of all �-MCSs;
� is the binary relation on �

� deﬁned by �

�

�� if for all formulas �,

� implies �

�

�

�. �

� is called the canonical relation.

�

�

(iii) �

� is the valuation deﬁned by �
the canonical (or natural) valuation.

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

�. �

� is called

The pair �

�

�

�

� �

�

� �

� is called the canonical frame for �. �

All three clauses deserve comment. First, the canonical valuation equates the truth
of a propositional symbol at � with its membership in �. Our ultimate goal is to
prove a Truth Lemma which will lift this ‘truth = membership’ equation to arbitrary
formulas.

Second, note that the states of �

� consist of all �-consistent MCSs. The signif-
icance of this is that, by Lindenbaum’s Lemma, any �-consistent set of formulas
� — hence, by the Truth Lemma proved below,
is a subset of some point in �
any �-consistent set of formulas is true at some point in this model. In short, the
� is a ‘universal model’ for the logic �, which is why it’s called
single structure �
‘canonical’.

Finally, consider the canonical relation: a state � is related to a state � precisely
when for each formula � in �, � contains the information �
�. Intuitively, this
captures what we mean by MCSs being ‘coherently related’. The reader should
compare the present discussion with the account of ultraﬁlter extensions in Chap-
ter 2 — in Chapter 5 we’ll discuss a unifying framework. In the meantime, the
following lemma shows that we’re getting things right:

Lemma 4.19 For any normal logic �, �
implies �

�.

�

�

�� iff for all formulas �, �

�

�

�

Proof. For the left to right direction, suppose �
is an MCS, by Proposition 4.16 �

�

��. Further suppose �

�. As �
�. As � is consistent,
� and we have established the contrapositive. We

�. As �

��, �

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

��

�

�. That is, �

�

��

leave the right to left direction to the reader. �

In fact, the deﬁnition of �
checked is that enough ‘coherently related’ MCSs exist for our purposes.

� is exactly what we require; all that remains to be

Lemma 4.20 (Existence Lemma) For any normal modal logic � and any state

�

�

�

�, if �

�

� then there is a state �

�

� such that �

�

�� and �

�

�.

�

�

Proof. Suppose �
� be �
Let �

�

�

�

�. We will construct a state � such that �

�.
� is consistent. For suppose not. Then

�� and �

�

�

�. Then �

� � �

�

�

�

�

�

�

4.2 Canonical Models

201

�

�

such that �

, . . . , �
there are �
easy argument that �
formula �
modal logic, hence by propositional calculus, �

� � � � �

� � � � �

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

� � � � �

� � � � �

�

�

�

�

� � � � �

�

� (for �

�

, . . . , �

�

�

�

�

�

�

�. Using Dual, it follows that �

�

�

�

�

�

� � �

�, and it follows by an
�� As the reader should check, the
� is a theorem of every normal
�. Now,
�, and � is an MCS) thus it follows
�. But this is impossible: � is

�� � ��

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

that �
an MCS containing �

�

�

�

�. We conclude that �

� is consistent after all.

Let � be any MCS extending �

�. Furthermore, for all formulas �, �

�; such extensions exist by Lindenbaum’s Lemma.
�.

� implies �

�

�

�

By construction �
Hence by Lemma 4.19, �

�

�

��. �

With this established, the rest is easy. First we lift the ‘truth = membership’ equa-
tion to arbitrary formulas:

Lemma 4.21 (Truth Lemma) For any normal modal logic � and any formula �,

�

�

�

� �

� iff �

�.

�

Proof. By induction on the degree of �. The base case follows from the deﬁnition
�. The boolean cases follow from Proposition 4.16. It remains to deal with the
of �
modalities. The left to right direction is more or less immediate from the deﬁnition
of �

�:

�

�

�

�

� �

�

iff
iff

�

�

�

�

�

�

��

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

��

�

�

only if �

�

�

�

(Induction Hypothesis)
(Deﬁnition �

�

�

For the right to left direction, suppose �
� such that �
sufﬁces to ﬁnd an MCS
the Existence Lemma guarantees. �

�

�

�

�� and �

�. By the equivalences above, it
� — and this is precisely what

�

Theorem 4.22 (Canonical Model Theorem) Any normal modal logic is strongly
complete with respect to its canonical model.

Proof. Suppose � is a consistent set of the normal modal logic �. By Linden-
� extending �. By the previous lemma,
baum’s Lemma there is a �-MCS

�

�

�

�

�

� �

�. �

At ﬁrst glance, the Canonical Model Theorem may seem rather abstract. It is a
completeness result with respect to a class of models, not frames, and a rather ab-
(That K4 is complete with respect to the class of transitive
stract class at that.
frames is interesting; that it is complete with respect to the singleton class contain-
ing only its canonical model seems rather dull.) But appearances are misleading:
canonical models are by far the most important tool used in the present chapter.
For a start, the Canonical Model Theorem immediately yields the following result:

202

4 Completeness

Theorem 4.23 K is strongly complete with respect to the class of all frames.

Proof. By Proposition 4.12, to prove this result it sufﬁces to ﬁnd, for any K-
consistent set of formulas � , a model � (based on any frame whatsoever) and a
state � in � such that �
�,
� be any K-MCS extending � . By the previous
the canonical model for K, and let �
lemma, �

� . This is easy: simply choose � to be �

� . �

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

More importantly, it is often easy to get useful information about the structure of
canonical frames. For example, as we will learn in the next section, the canonical
frame for K4 is transitive — and this immediately yields the (more interesting)
result that K4 is complete with respect to the class of transitive frames. Even when
a canonical model is not as cleanly structured as we would like, it still embod-
ies a vast amount of information about its associated logic; one of the important
themes pursued later in the chapter is how to make use of this information in-
directly. Furthermore, canonical models are mathematically natural. As we will
learn in Chapter 5, from an algebraic perspective canonical models are not abstract
oddities: indeed, they are precisely the structures one is lead to by considering the
ideas underlying the Stone Representation Theorem.

To conclude this section we sketch the generalizations required to extend the results
obtained so far to languages of arbitrary similarity types.

Deﬁnition 4.24 Let � be a modal similarity type, and � a normal modal logic in
the language over � . The canonical model �
for � has
� the
,

� as deﬁned in Deﬁnition 4.18, while for an �-ary operator �
if for all formulas �

�� is deﬁned by �

� � �

� � � �

� �

��

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

we have �

�

�

� � � � � �

� �

�. �

�

�

�

�

� and �
relation �
. . . , �

�

�

�

�

�

�

There is an analog of Lemma 4.19.

Lemma 4.25 For any normal modal logic �, �

�

�

��

� � � �

�

�

� implies that for some � such that � �

iff for all formulas
�,

�

�

�

� � � � � �

, �

�

� �

�

� � � � � �

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

Proof. See Exercise 4.2.3. �

Now for the crucial lemma — we must show that enough coherently related MCSs
exist. This requires a more delicate approach than was needed for Lemma 4.20.

Lemma 4.26 (Existence Lemma) Suppose �

�

�

� � � � � �

�

�

� �

�. Then there are

, . . . , �

such that �

�

, . . . , �

�

�

and �

�

�

�

��

� � � �

.

�

�

�

�

�

�

�

�

Proof. The proof of Lemma 4.20 establishes the result for any unary operators in
the language, so it only remains to prove the (trickier) case for modalities of higher

4.3 Applications

203

arity. To keep matters simple, assume that � is binary; this illustrates the key new
idea needed.

So, suppose �

�

� �

�

� �

�. Let �

, �

, . . . enumerate all formulas. We con-

�

�

�

�

struct two sequences of sets of formulas

�

� �

�

�

�

�

� � � � and �

�

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

such that all �

and �
�, and similarly for �

are ﬁnite and consistent, �
. Moreover, putting �

�

�

�

��

is either �

� �

�

�

�

and �

��

� or
,

�

�

�

���

�

�

�

��

�

�

�

�

��

�

we will have that �

�

�

� �

� �

�

�

�.

The key step in the inductive construction is

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

� �

� �

�� �

�

� �

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

��

�

� � �

� �

�

�

�

� � �

� �

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

�

�

�

�

�

�

�

�

� one of the formulas �

�

� ���

� ���

�

�

� �

�

�

�

�

�

� is in �.

�, we take �
and �

�

�

If, for example, �

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

��

� �

�

�

�, �

��

��

��

�

�

�

�

�

�

� ��

�

�

Finally, let �
and �

��

�

�

�

�

�. Under this deﬁnition, all �
and �

�

�

�

�

. It is easy to see that �

have the required properties.
are �-MCSs
, �

�

�

�

�

�

�

�

, as required. �

�

�

�

�

With this lemma established, the real work has been done. The Truth Lemma
and the Canonical Model Theorem for general modal languages are now obvious
analogs of Lemma 4.21 and Theorem 4.22. The reader is asked to state and prove
them in Exercise 4.2.4.

Exercises for Section 4.2
4.2.1 Show that all MCSs have the properties stated in Proposition 4.16. In addition, show
that if � and � are distinct MCSs, then there is at least one formula � such that �
� and

�

� .

�

�

�

4.2.2 Lindenbaum’s Lemma is not fully proved in the text. Give proofs of the four claims
made at the end of our proof sketch.

4.2.3 Prove Lemma 4.25. (This is a good way of getting to grips with the deﬁnition of
normality for modal languages of arbitrary similarity type.)

4.2.4 State and prove the Truth Lemma and the Canonical Model Theorem for languages
of arbitrary similarity type. Make sure you understand the special case for nullary modali-
ties (recall that we have no special axioms or rules of proof for these).

4.3 Applications
In this section we put canonical models to work. First we show how to prove
the frame completeness results noted in Example 4.11 using a simple and uniform

204

4 Completeness

method of argument. This leads us to isolate one of most important concepts of
modal completeness theory: canonicity. We then switch to the basic temporal
language and use similar arguments to prove two important temporal completeness
results. We conclude with a statement of the Sahlqvist Completeness Theorem,
which we will prove in Chapter 5.

Suppose we suspect that a normal modal logic � is strongly complete with re-
spect to a class of frames �; how should we go about proving it? Actually, there is
no infallible strategy. (Indeed, as we will learn in the following section, many nor-
mal modal logics are not complete with respect to any class of frames whatsoever.)
Nonetheless, a very simple technique works in a large number of interesting cases:
simply show that the canonical frame for � belongs to �. We call such proofs
completeness-via-canonicity arguments, for reasons which will soon become clear.
Let’s consider some examples.

Theorem 4.27 The logic K4 is strongly complete with respect to the class of tran-
sitive frames.

�

� �

��

��

��

� �

� be the canonical model for K4 and let �

Proof. Given a K4-consistent set of formulas � , it sufﬁces to ﬁnd a model �
and a state � in this model such that (1) �
Let �
MCS extending � . By Lemma 4.21, �
established. It remains to show that �
and � are points in this frame such that �
��, �

� , and (2) � is transitive.
� be any K4-
� so step (1) is
� is transitive. So suppose �, �
��. We wish to show that
�. But � is
��, ��
�.
�, thus by modus ponens it contains �

�� and �
�, so as �

��. Suppose �

�. As �

�

�

�

�

� �

�

� �

� �

��

� �

��

��

��

��

��

��

��

��

��

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

a K4-MCS, hence it contains ��
Thus �

��. �

��

In spite of its simplicity, the preceding result is well worth reﬂecting on. Two
important observations should be made.

First, the proof actually establishes something more general than the theorem

claims: namely, that the canonical frame of any normal logic � containing ��

�

�

�

� is transitive. The proof works because all MCSs in the canonical frame contain
the 4 axiom; it follows that the canonical frame of any extension of K4 is transitive,
for all such extensions contain the 4 axiom.

Second, the result suggests that there may be a connection between the structure
of canonical frames and the frame correspondences studied in Chapter 3. We know
� deﬁnes transitivity — and now we know
from our previous work that ��
that it imposes this property on canonical frames as well.

�

�

�

Theorem 4.28 T, KB and KD are strongly complete with respect to the classes of
reﬂexive frames, of symmetric frames, and of right-unbounded frames, respectively.

4.3 Applications

205

Proof. For the ﬁrst claim, it sufﬁces to show that the canonical model for � is
�. As � is a T-MCS,
reﬂexive. Let � be a point in this model, and suppose �

�

�

�

�

�

�

�, thus by modus ponens, �

�

�

�. Thus �

�

��.

�

�

�

�

�

�

��

��

�. As � is a KB-MCS, �

�, thus by modus ponens ��
��, as required.

For the second claim, it sufﬁces to show that the canonical model for �� is
��, and suppose
�.

symmetric. Let � and � be points in this model such that �
that �
Hence by Lemma 4.19, �

�. But this means that �
For the third claim, it sufﬁces to show that the canonical model for �� is right-
unbounded. (This is slightly less obvious than the previous claims since it requires
an existence proof.) Let � be any point in the canonical model for ��. We
must show that there exists a � in this model such that �
��. As � is a ��-
�, thus by closure under uniform substitution it contains
MCS it contains �
�. Moreover, as � belongs to all normal modal logics, by generalization
�. Hence,

� belongs to ��, hence by modus ponens �

� does too; so �

� �

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

by the Existence Lemma, � has an �

�� successor �. �

Once again, these result hint at a link between deﬁnability and the structure of
canonical frames: after all, T deﬁnes reﬂexivity, B deﬁnes symmetry, and D right
unboundedness. And yet again, the proofs actually establish something more gen-
eral than the theorem states: the canonical frame of any normal logic containing
T is reﬂexive, the canonical frame of any normal logic containing B is symmetric,
and the canonical frame of any normal logic containing D is right unbounded. This
allows us to ‘add together’ our results. Here are two examples:

Theorem 4.29 S4 is strongly complete with respect to the class of reﬂexive, tran-
sitive frames. S5 is strongly complete with respect to the class of frames whose
relation is an equivalence relation.

Proof. The proof of Theorem 4.27 shows that the canonical frame of any normal
logic containing the 4 axiom is transitive, while the proof of the ﬁrst clause of
Theorem 4.28 shows that the canonical frame of any normal logic containing the
T axiom is reﬂexive. As S4 contains both axioms, its canonical frame has both
properties, thus the completeness result for S4 follows.

As S5 contains both the 4 and the T axioms, it also has a reﬂexive, transitive
canonical frame. As it also contains the B axiom (which by the proof of the second
clause of Theorem 4.28 means that its canonical frame is symmetric), its canonical
relation is an equivalence relation. The desired completeness result follows. �

As these examples suggest, canonical models are an important tool for proving
frame completeness results. Moreover, their utility evidently hinges on some sort
of connection between the properties of canonical frames and the frame corre-
spondences studied earlier. Let us introduce some terminology to describe this
important phenomenon.

206

4 Completeness

Deﬁnition 4.30 (Canonicity) A formula � is canonical if, for any normal logic
�, �
� implies that � is valid on the canonical frame for �. A normal logic � is
canonical if its canonical frame is a frame for �. (That is, � is canonical if for all
� such that �

�, � is valid on the canonical frame for �.) �

�

�

Clearly 4, T, B and D axioms are all canonical formulas. For example, any normal
logic � containing the 4 axiom has a transitive canonical frame, and the 4 axiom is
valid on transitive frames. Similarly, any modal logic containing the B axiom has
a symmetric canonical frame, and the B axiom is valid on symmetric frames.

Moreover K4, T, KB, KD, S4 and S5 are all canonical logics. Our previous
work has established that all the axioms involved are valid on the relevant canonical
frames. But (see Exercise 4.1.1) modus ponens, uniform substitution, and general-
ization preserve frame validity. It follows that every formula in each of these logics
� is a
is valid on that logic’s canonical frame. In general, to show that ��
canonical logic it sufﬁces to show that �

are canonical formulas.

� � � � � �

� � �

�

�

�

�

Deﬁnition 4.31 (Canonicity for a Property) Let � be a formula, and � be a prop-
erty. If the canonical frame for any normal logic � containing � has property � ,
and � is valid on any class of frames with property � , then � is canonical for � .
For example, we say that the 4 axiom is canonical for transitivity, because the pres-
ence of 4 forces canonical frames to be transitive, and 4 is valid on all transitive
frames. �

Let us sum up the discussion so far. Many important frame completeness results
can be proved straightforwardly using canonical models. The key idea in such
proofs is to show that the relevant canonical frame has the required properties.
Such proofs boil down to the following task: showing that the axioms of the logic
are canonical for the properties we want (which is why we call them completeness-
via-canonicity arguments).

Now for some rather different application of completeness-via-canonicity argu-
ments. The theorems just proved were syntactically driven: we began with syn-
tactically speciﬁed logics (for example K4 and T) and showed that they could be
semantically characterized as the logics of certain frame classes. Canonical models
are clearly useful for such proofs — but how do they fare when proving semanti-
cally driven results? That is, suppose � is a class of frames we ﬁnd interesting, and
we have isolated a set of axioms which we hope generates �F. Can completeness-
via-canonicity arguments help establish their adequacy?

As such semantically driven questions are typical of temporal logic, let us switch
to the basic temporal language. Recall from Example 1.14 that this language has
two diamonds, � and � , whose respective duals are � and �. The � operator
looks forward along the ﬂow of time, and � looks backwards. Furthermore, recall
from Example 1.25 that we are only interested in the frames for this language in

4.3 Applications

207

which the relations corresponding to � and � are mutually converse. That is, a
bidirectional frame is a triple �

�� such that

� �

��

�

�

�

�

�

� � �

�� �

�

�

� ��

� � �

� �

�

�

�

�

� � �

Recall that by convention we present bidirectional frames as unimodal frames
�. The
, and a bidirectional model is a

�; in such presentations we understand that �

� and �

class of all bidirectional frames is denoted by �
model whose underlying frame belongs to �

.

�

�

�

�

�

�

So, what is a temporal logic? As a ﬁrst step towards answering this we deﬁne:

�

Deﬁnition 4.32 The minimal temporal logic �F�

is �

�

�

�

�

�

�

�. �

That is, the minimal temporal logic contains precisely the formulas valid on all
bidirectional frames. This is a semantic deﬁnition, and, given our interest in frames,
� a simple syn-
a sensible one. But can we axiomatize �
�? That is, can we give �
� is not identical to the minimal normal
tactic characterization? First, note that �
logic in the basic temporal language. As we noted in Example 1.29(v), for any
frame �

�� we have that

� �

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

� � �

�

�� �

�

�

� � �

�

� iff �

�

�

�

�

�

. Clearly, both conjuncts belong to �F�

The two conjuncts deﬁne the ‘mutually converse’ property enjoyed by �

and
. Equally clearly, they do not belong
to the minimal normal logic in the basic temporal language Nonetheless, although
is stronger, it is not much stronger: the only axioms we need to add are these

�

�

�F�
converse-deﬁning conjuncts.

Deﬁnition 4.33 A normal temporal logic � is a normal modal logic (in the basic
� � � (the converse axioms).
temporal language) that contains �
. We usually call normal temporal
The smallest normal temporal logic is called K�
logics tense logics.

�� � and �

�

�

Note that in the basic temporal language the K axioms are �
� and �

�, and the Dual axioms are � �

� � �

� �

� �

�

�

�

�

�

��

� �

�

�

�

� � �

�

�

�

��

�. Closure under generalization means that if �

� then �

�

�

� �

�

� �

�

� �. �

�

�

�

� and
�� and

generates exactly the formulas in �
�. Soundness is
We want to show that K�
�. We show completeness using a canonicity argument.
immediate: clearly K�
So, what are canonical models for tense logics? Nothing new: simply the following
instance of Deﬁnition 4.24:

�

�

�

�

Deﬁnition 4.34 The canonical model for a tense logic � is the structure �

�

�

�

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

� where:

208

4 Completeness

� is the set of all �-MCSs;

(i) �
(ii) �

�

is the binary relation on �

� deﬁned by �

�

�� if for all formulas �, �

�

�

�

�

implies � �

�.

�

(iii) �

�

is the binary relation on �

� deﬁned by �

�

�� if for all formulas �, �

�

�

�

�

implies � �

�.

�

(iv) �

� is the valuation deﬁned by �

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

�. �

�

We immediately inherit a number of results from the previous section, such as an
Existence Lemma, a Truth Lemma, and a Canonical Model Theorem telling us that
each tense logic is complete with respect to its canonical model. This is very useful
generates all the temporal
— but it is not quite enough. We want to show that �
validities. None of the results just mentioned allow us to conclude this, and for a
very obvious reason: we don’t yet know whether canonical frames for tense logics
are bidirectional frames! In fact they are, and this is where the converse axioms
come into play. As the next lemma shows, these axioms are canonical; they force

�

�

�

and �

�

to be mutually converse.

�

�

Lemma 4.35 For any tense logic �, if �

�

�� then �

�

��, and if �

�

�� then �

�

��.

�

�

�

�

Proof. Rather like the proof that B is canonical for symmetry (see Theorem 4.28
item (ii)). We leave it to the reader as Exercise 4.3.2. �

Thus canonical frames of tense logics are bidirectional frames, so from now on we
present them as pairs �

�. Moreover, we now have the desired result:

� �

�

�

�

Corollary 4.36 K�
tional frames, and K�

.

�F�

�

is strongly complete with respect to the class of all bidirec-

Proof. K�
is strongly complete with respect to its canonical model. As we’ve just
seen, this model is based on a bidirectional frame, so the strong frame complete-
.
ness result follows. Strong completeness implies weak completeness, so �F�
� has already been noted. �
The inclusion K�

� K�

�

�

�

With this basic result established, we are ready to start a semantically driven ex-
ploration of tense logic. That is, we can now attempt to capture the logics of ‘time-
. Here we limit ourselves to
like’ classes of frames as axiomatic extensions of K�
the following question: how can the temporal logic of dense unbounded weak total
orders be axiomatized? From the point of view of tense logic, this is an interesting
problem: dense frames and totally ordered frames both play an important role in
modeling temporal phenomena. Moreover, as we will see, there is an instructive
problem that must be overcome if we build totally ordered models. This will give
us a gentle initiation to the fundamental difﬁculty faced by semantically driven
completeness results, a difﬁculty which we will explore in more detail later in the
chapter.

4.3 Applications

209

�

��

���

� � �

� is dense if there is a point between
Deﬁnition 4.37 A bidirectional frame �
��). It is right-unbounded if
any two related points (�
every point has a successor, left-unbounded if every point has a predecessor, and
unbounded if it is both right and left unbounded.
It is trichotomous if any two
points are equal or are related one way or the other (�
�),
and a weak total order (or weakly linear) if it is both transitive and trichotomous.
We call a frame with all these properties a DUWTO-frame. �

� �

���

���

���

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

�� �

�, ���

Note that weakly linear frames are allowed to contain both reﬂexive and irreﬂexive
points. Indeed, they are allowed to contain non-empty subsets � such that for all
�. Thus they do not fully model the idea of linearity. Linearity is
better captured by the class of strict total orders, which are transitive, trichotomous
and irreﬂexive. Building strictly totally ordered models is harder than building
weakly totally ordered models; we examine the problem in detail later in the chap-
ter.

Our ﬁrst task is to select suitable axioms. Three of the choices are fairly obvious.

(4)
(D
(D

� � �

� �

�

�

) ��
) � �

�

� �

�

� �

�

�

Note that � � �
� � is simply the 4 axiom in tense logical notation. We know
(by the proof of Theorem 4.27) that it is canonical for transitivity, hence choosing
(a tense
it as an axiom ensures the transitive canonical frame we want. Next, D
logical analog of the D axiom) is (by the proof of the third claim of Theorem 4.28)
canonical for right-unboundedness. Similarly, its backward-looking companion
� � is canonical for left-unboundedness, so we obtain an unbounded canon-

� �

�

�

ical frame without difﬁculty.

What about density? Here we are in luck. The following formula is canonical

for density:

(Den) � �

�

� � �

This is worth a lemma, since the proof is not trivial.
(Note that density is a
universal-existential property, rather than a universal property like transitivity or
reﬂexivity. This means that proving canonicity requires establishing the existence
of certain MCSs.)

Lemma 4.38 � �

�

� � � is canonical for density.

Proof. Let � be any tense logic containing � �
ical frame, and let � and �
show that there is a �-MCS

� such that �

�

� � �, let �

�

�

�

�

� �

� be its canon-
�. We have to
�. If we could show that

��

�

�� and �

�

��

� be points in this frame such that �

210

4 Completeness

�

�

�

�

�

��

� was consistent we would have the desired result
(for by Lemma 4.35, any MCS extending this set would be a suitable choice for �).
So suppose for the sake of contradiction that this set is not consistent. Then, for

� � �

� �

�

�

�

�

�

some ﬁnite set of formulas �

� � � � � �

� �

� � � � � �

from this set,

�

�

�

�

�

�

� � � � �

�

� � � � �

� ��

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

. Note that
��, hence �

�

�.

�

�

Deﬁne

� to be �

� � � � �

�

�

and

� to be �

� � � � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

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

� � � � �

, . . . , ��

, hence �

�, and hence �

�. Because ��

Now, �
and hence �
too, hence �
means that �
now we have a contradiction: as
that �
makes no use of the converse axioms, thus we have also proved that �
is canonical for density.) �

�. But this
�. But
� must be in �. We conclude
� is consistent after all. (Note that this proof

�, as (by uniform substitution in Den) �

�, we have that �

�. That is, � �

�,

� �

�

� and �

�, �

�

�

� � �

� �

� �

��

�

�

��

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

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

So it only remains to ensure trichotomy — but here we encounter an instructive dif-
ﬁculty. Because modal (and temporal) validity is preserved under the formation of
disjoint unions (see Proposition 3.14) no formula of tense logic deﬁnes trichotomy.
Moreover, a little experimentation will convince the reader that canonical frames
may have disjoint point generated subframes; such canonical frames are clearly
not trichotomous. In short, to prove the desired completeness result we need to
build a model with a property for which no modal formula is canonical. This is
the problem we encounter time and time again when proving semantically driven
results.

In the present case, a little lateral thinking leads to a solution. First, let us get rid
of a possible preconception. Until now, we have always used the entire canonical
model — but we do not need to do this. A point generated submodel sufﬁces. More
� , then as modal satisfaction is preserved in generated
precisely, if �
submodels (see Proposition 2.6) �
generated by �.

� , where � is the submodel of �

� �

� �

�

�

�

�

The observation is trivial, but its consequences are not. By restricting our at-
tention to point-generated submodels, we increase the range of properties we can
impose. In particular, we can impose trichotomy on point-generated submodels.
We met the relevant axioms when working with the basic modal language. From
our discussion of S4.3 and K4.3 (in particular, Exercise 4.3.3) we know that

(.3

�

)

�

�

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

� �

is canonical for no-branching-to-the-right. Analogously

(.3

)

�

�

�

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

� �

�

4.3 Applications

211

is canonical for no-branching-to-the-left. Call a frame with no branching to the left
or right a non-branching frame.

Proposition 4.39 Any trichotomous frame �
if � is transitive and non-branching and �
erated by � is trichotomous.

�

� � �

� is non-branching. Furthermore,
� gen-

� , then the subframe of �

� � �

Proof. Trivial — though the reader should recall that when forming generated sub-
frames for the basic temporal language, we generate on both the relation corre-
sponding to � and that corresponding to � . That is, we generate both forwards
and backwards along �. �

In short, although no formula is canonical for trichotomy, there is a good ‘ap-
proximation’ to it (namely, the non-branching property) for which we do have a
). With this observed, the
canonical formula (namely, the conjunction of �
desired result is within reach.

and �

�

�

�

�

Deﬁnition 4.40 Let K�Q be the smallest tense logic containing 4, D
and �

. �

�

�

, D

�

, Den, �

�

�

�

Theorem 4.41 K�Q is strongly complete with respect to the class of DUWTO-
frames.

Proof. If � is K�Q-consistent set of formulas, extend it to a K�Q-MCS
�. Let �
�.
be the canonical model for K�Q, and let � be the submodel of � generated by �
� . Moreover, the frame underlying � is a DUWTO-
As we just noted, �
frame as required. First, as K�Q contains axioms that are canonical for transitivity,
unboundedness, and density, � has these properties; it is then not difﬁcult to show
is canonical for
that � has them too. Moreover, as the conjunction of �
non-branching, � is non-branching and � trichotomous. �

and �

� �

�

�

�

�

�

�

�

To conclude, two important remarks. First, the need to build models possessing
properties for which no formula is canonical is the fundamental difﬁculty facing
semantically driven results. In the present case, a simple idea enabled us to bypass
the problem — but we won’t always be so lucky and in the second part of the
chapter we develop more sophisticated techniques for tackling the issue.

Second, the relationships between completeness, canonicity and correspondence
are absolutely fundamental to the study of normal modal logics. These relation-
ships are further discussed in the following section, and explored algebraically in
Chapter 5, but let’s immediately mention one of the most elegant positive results
in the area:
In Chapter 3 we proved the
Sahlqvist Correspondence Theorem: every Sahlqvist formula deﬁnes a ﬁrst-order
class of frames. Here’s its completeness theoretic twin, which we will prove in
Chapter 5:

the Sahlqvist Completeness Theorem.

212

4 Completeness

Theorem 4.42 Every Sahlqvist formula is canonical for the ﬁrst-order property
it deﬁnes. Hence, given a set of Sahlqvist axioms �, the logic K� is strongly
complete with respect to the class of frames �
(that is, the ﬁrst-order class of
frames deﬁned by �).

�

This is an extremely useful result. Most commonly encountered axioms in the
basic modal language are Sahlqvist (the L¨ob and McKinsey formulas are the ob-
vious exceptions) thus it provides an immediate answer to a host of completeness
problems. Moreover, like the Sahlqvist Correspondence Theorem, the Sahlqvist
Completeness Theorem applies to modal languages of arbitrary similarity type.
Finally, the Theorem generalizes to a number of extended modal logics, most no-
tably �-logic (which we introduce in Chapter 7). Note that Kracht’s Theorem (see
Chapter 2) can be viewed as a providing a sort of ‘converse’ to Sahlqvist’s result,
for it gives us a way of computing formulas that are canonical for certain ﬁrst-order
classes of frames.

Exercises for Section 4.3
4.3.1 Let �
with respect to the class of all frames �

� be the axiom �

�

�

�

�

�. Show that ��

� is sound and strongly complete

�

� such that � is a partial function.

�� �

4.3.2 Let � be a normal temporal logic containing the axioms �
��, and if �
Show that if �

�� then �

�� then �

��.

�

�

�

�

�� � and �

�

� � �.

�

�

�

�

�

4.3.3 Use canonical models to show that K4.3 is strongly complete with respect to the
class of frames that are transitive and have no branching to the right, and that S4.3 is
strongly complete with respect to the class of frames that are reﬂexive, transitive and have
no branching to the right.

Then, by proving suitable completeness results (and making use of the soundness results

proved in Exercise 4.1.4), show that the normal logic axiomatized by �

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

�

�

�

��

�

�

�

� is K4.3. Further, show that the normal modal logic axiomatized by
� is S4.3. Try proving the equivalence of these logics syntactically.

�

�

�

�

4.3.4 Prove directly that ��

�

�

��

� is canonical for the Church-Rosser property.

4.3.5 Let W5 be the formula ��
�, and let S4W5 be the smallest normal
logic extending S4 that contains W5. Find a simple class of frames that characterizes this
logic.

� �

�

�

�

�

�

4.3.6 Show that S5 is complete with respect to the the class of globally related frames,
that is, those frames �
� ���.

� such that �

�� �

4.3.7 Consider a similarity type � with one binary operator �. For each of the following
Sahlqvist formulas, ﬁrst compute the (global) ﬁrst-order correspondent. Then, give a direct
proof that the modal formula is canonical for the corresponding ﬁrst-order property.

(a) �
(b) �
(c) ��

�

�

�

�

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

�

�

�

�

�

�

�

��

�� �

�

�,
� � �.

�

4.4 Limitative Results

213

4.4 Limitative Results

Although completeness-via-canonicity is a powerful method, it is not infallible.
For a start, not every normal modal logic is canonical. Moreover, not every normal
logic is the logic of some class of frames. In this section we prove both claims and
discuss their impact on modal completeness theory.

We ﬁrst demonstrate the existence of non-canonical logics. We will show that
�,
KL, the normal modal logic generated by the L¨ob axiom �
is not canonical. We prove this by showing that KL is not sound and strongly
complete with respect to any class of frames. Now, every canonical logic is sound
and strongly complete with respect to some class of frames. (For suppose � is a
canonical logic and � is a �-consistent set of formulas. By the Truth Lemma, � is
satisﬁable on �
� is a frame for �.) Hence if KL is not sound
and strongly complete with respect to any class of frames, it cannot be canonical
either.

�; as � is canonical, �

� �

�

�

�

�

�

�

Theorem 4.43 KL is not sound and strongly complete with respect to any class of
frames, and hence it is not canonical.

Proof. Let � be �
�. We will show that � is
KL-consistent, and that no model based on a KL-frame can satisfy all formulas in
� at a single point. The theorem follows immediately.

� � � �

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

�

�

�

�

�

To show that � is consistent, it sufﬁces to show that every ﬁnite subset � of � is
consistent. Given any such � , for some natural number � there is a ﬁnite set � of
� . We show
the form �
that �, and hence � , is consistent.

� such that �

� � � �

� � �

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

�

�

�

�

�

�

Let

� be the conjunction of all the formulas in �. To show that

� is KL-
consistent, it sufﬁces to show that it can be satisﬁed in a model based on a frame for
� is not valid on all frames for KL, and hence is not one
KL, for this shows that �
of its theorems. Let � be the frame consisting of ��
� in their usual order; as
this is a transitive, converse well-founded frame, by Example 3.9 it is a frame for
KL. Let � be any model based on � such that for all � �
�.
� is KL consistent.
Then �

� and

�, �

� � � � � �

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

Next, suppose for the sake of a contradiction that KL is sound and strongly com-
plete with respect to some class of frames �; note that as KL is not the inconsistent
logic, � must be non-empty. Thus any KL-consistent set of formulas can be satis-
ﬁed at some point in a model based on a frame in �. In particular, there is a model
� . But this is
� based on a frame in � and a point � in � such that �
� , we can inductively deﬁne an inﬁnite path through
impossible: because �
� starting at �; however as � is based on a frame for �� it cannot contain such
inﬁnite paths. Hence KL is not sound and strongly complete with respect to any
class of frames, and so cannot be canonical. �

� �

� �

�

�

214

4 Completeness

Remark 4.44 A normal logic � is said to be compact when any �-consistent set
� can be satisﬁed in a frame for � at a single point. So the above proof shows that
KL is not compact. Note that a non-compact logic cannot be canonical, and cannot
be sound and strongly complete with respect to any class of frames. We will see a
similar compactness failure when we examine PDL in Section 4.8. �

What are we to make of this result? The reader should not jump to the conclusion
that it is impossible to characterize KL as the logic of some class of frames. Al-
though no strong frame completeness result is possible, as we noted in Table 4.1
there is a elegant weak frame completeness result for KL, namely:

Theorem 4.45 KL is weakly complete with respect to the class of all ﬁnite transi-
tive trees.

Proof. The proof uses the ﬁnitary methods studied later in the chapter. The reader
is asked to prove it in Exercises 4.8.7 and 4.8.8. �

Thus KL is the logic of all ﬁnite transitive trees — and there exist non-canonical
but (weakly) complete normal logics. We conclude that, powerful though it is, the
completeness-via-canonicity method cannot handle all interesting frame complete-
ness results.

Let us turn to the second conjecture: are all normal logics weakly complete with

respect to some class of frames? No: incomplete normal logics exist.

Deﬁnition 4.46 Let � be a normal modal logic. � is (frame) complete if there is a
class of frames F such that �

�F, and (frame) incomplete otherwise. �

�

We now demonstrate the existence of incomplete logics in the basic temporal lan-
guage. The demonstration has three main steps. First, we introduce a tense logic
called K�Tho and show that it is consistent. Second, we show that no frame
for K�Tho can validate the McKinsey axiom (which in tense logical notation is
� ��). It is tempting to conclude that K�ThoM, the smallest tense logic
containing both K�Tho and the McKinsey axiom, is the inconsistent logic. Sur-
prisingly, this is not the case. K�ThoM is consistent — and hence is not the tense
logic of any class of frames at all. We prove this in the third step with the help of
general frames.

�� �

�

K�Tho is the tense logic generated by the following axioms:

(.3
(D
(L

�

�

)
)
)

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

� �

�

�

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

��

� �

�

�

� �

�

� �

�

�

� �

�

As we have already seen, the ﬁrst two axioms are canonical for simple ﬁrst-order
conditions (no branching to the right, and right-unboundedness, respectively). The

4.4 Limitative Results

215

third axiom is simply the L¨ob axiom written in terms of the backward looking
operator �; it is valid on precisely those frames that are transitive and contain no
inﬁnite descending paths. (Note that such frames cannot contain reﬂexive points.)
Let K�Tho be the tense logic generated by these three axioms. As all three axioms
� is a frame for
are valid on the natural numbers, K�Tho is consistent.
K�Tho and �

� is a right-unbounded strict total order.

� , then �

If �

� � �

���

�

�

�

�

�

Now for the second step. Let K�ThoM be the smallest tense logic containing
� ��. What are the frames for this
K�Tho and the McKinsey axiom �� �
enriched logic? The answer is: none at all, or, to put it another way, K�ThoM
deﬁnes the empty class of frames. To see this we need the concept of coﬁnality.

�

Deﬁnition 4.47 Let �
for every �

�

� there is an �

� such that � � �. �

�

� be a strict total order and �

� . � is coﬁnal in � if

�

�� �

For example, both the even numbers and the odd numbers are coﬁnal in the natural
numbers. Indeed, they are precisely the kind of coﬁnal subsets we will use in the
work that follows: mutually complementary coﬁnal subsets.

Lemma 4.48 Let � be any frame for K�Tho. Then �

�

�� �

�

� ��.

Proof. Let � be any point in �, let �
�, and let � be the restriction
of � to � . As �, validates all the K�Tho axioms, �
� is a right-unbounded strict
total order. Suppose we could show that there is a non-empty proper subset � of
� are coﬁnal in � . Then the lemma would be proved,
� such that both � and �
�, and
for we would merely need to deﬁne a valuation � on � such that �

�� �

���

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

� �

� �

�� �

�

� ��.

Such subsets � of � exist by (3.18) in Chapter 3. For a more direct proof, take
an ordinal � that is larger than the size of � . By ordinal induction, we will deﬁne
and
a sequence of pairs of sets �
. The

are coﬁnal. We can easily prove the lemma from this by taking �

� and both �

such that �

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

deﬁnition is as follows:

(i) For �

� �, take some points �

and �

in � such that �

and deﬁne

� �

�

�

�

�

�.
(ii) If � is a successor ordinal �

� and �

� �

� �

�

�

�

�

�

�

�

� �, then distinguish two cases:

�

or �

(a) if �
(b) if neither �
(that is, �

�

�

nor �
� � for all �

�

is coﬁnal, then deﬁne �

and �

,

�

�

�

�

�

�

�

�

�

�

is coﬁnal, then take some upper bound �

), take some �

bigger than �

�

�

of
and

�

�

�

�

�

deﬁne �

�

� �

�

�

� and �

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

(iii) If � is a limit ordinal, then deﬁne �

�

�

and �

�

�

�

�

�

�

.

���

���

It is easy to prove that �
and �
shown that both �

�

�

�

�

�

� for every ordinal �

�, so it remains to be
are coﬁnal. The key to this proof is the observation that

�

�

�

�

�

�
�
216

4 Completeness

�

and �

were not coﬁnal, then the (implicitly deﬁned) partial map �

if �
would be total and injective (further proof details are left to the reader). This would
contradict the assumption that � exceeds the size of � . �

�

�

�

�

�

We are ready for the ﬁnal step. As K�ThoM deﬁnes the empty class of frames, it is
tempting to conclude that it is also complete with respect to this class; that is, that
K�ThoM is the inconsistent logic. However, this is not the case.

Theorem 4.49 K�ThoM is consistent and incomplete.

�

� �

Proof. Let �
� be the natural numbers in their usual order. Let � be the col-
lection of ﬁnite and coﬁnite subsets of �; we leave it to the reader to show that
� is closed under boolean combinations and modal projections. Thus �
� is
a general frame; we claim that it validates all the K�ThoM axioms. Now, it cer-
tainly validates all the K�Tho axioms, for these are already valid on the underlying
� �� cannot be
frame. But what about M? As we noted in Example 1.34, �� �
falsiﬁed under assignments mapping � to either a ﬁnite or a co-ﬁnite set. Hence all
the axioms are valid and K�ThoM must be consistent.

� �� �

�

�

Now, by Lemma 4.48, K�ThoM is not the logic of any non-empty class of
frames. But as K�ThoM is consistent, it’s not the logic of the empty class of
frames either. In short, it’s not the logic of any class of frames whatsoever, and is
incomplete. �

Frame incompleteness results are not some easily ﬁxed anomaly. As normal logics
are sets of formulas closed under three rules of proof, the reader may be tempted to
think that these rules are simply too weak. Perhaps there are yet-to-be-discovered
rules which would strengthen our deductive apparatus sufﬁciently to overcome in-
completeness? (Indeed, later in the chapter we introduce an additional proof rule,
and it will turn out to be very useful.)

Nonetheless, no such strengthening of our deductive apparatus can eliminate
frame incompleteness. Why is this? Ultimately it boils down to something we
learned in Chapter 3: frame consequence is an essentially a second-order relation.
Moreover, as we discussed in the Notes to Chapter 3, it is a very strong relation
indeed: strong enough to simulate the standard second-order consequence rela-
tion. Frame incompleteness results reﬂect the fact that (over frames) modal logic
is second order logic in disguise.

There are many incomplete logics. Indeed, if anything, incomplete logics are
the norm. An analogy may be helpful. When differential calculus is ﬁrst encoun-
tered, most students have rather naive ideas about functions and continuity; poly-
nomials, and other simple functions familiar from basic physics, are taken to be
typical of all real-valued functions. The awakening comes with the study of anal-
ysis. Here the student encounters such specimens as everywhere-continuous but

4.4 Limitative Results

217

nowhere-differentiable functions — and comes to see that the familiar functions
are actually abnormally well-behaved. The situation is much the same in modal
logic. The logics of interest to philosophers — logics such as T, S4 and S5 —
were the ﬁrst to be semantically characterized using frames. It is tempting to be-
lieve that such logics are typical, but they are actually fairly docile creatures; the
lattice of normal logics contains far wilder inhabitants.

The signiﬁcance of the incompleteness results depends on one’s goals. Logi-
cians interested in applications are likely to focus on certain intended classes of
models, and completeness results for these classes. Beyond providing a salutary
warning about the folly of jumping to hasty generalizations, incompleteness results
are usually of little direct signiﬁcance here. On the other hand, for those whose pri-
mary interest is syntactically driven completeness results, the results could hardly
be more signiﬁcant: they unambiguously show the inadequacy of frame-based clas-
siﬁcations. Unsurprisingly, this has had considerable impact on the study of modal
logic. For a start, it lead to a rebirth of interest in alternative tools — and in partic-
ular, to the renaissance of algebraic semantics, which we will study in Chapter 5.
Moreover, it has lead modal logicians to study new types of questions. Let us
consider some of the research themes that have emerged.

One response has been to look for general syntactic constraints on axioms which
guarantee canonicity. The most elegant such result is the Sahlqvist Completeness
Theorem, which we have already discussed. A second response has been to investi-
gate the interplay between completeness, canonicity, and correspondence. Typical
are axioms that
of the questions that can be posed is the following: If �
� frame complete? (In fact,
deﬁne an elementary class of frames, is ��
the answer here is no — as the reader is asked to show in Exercise 4.4.3.) The
most signiﬁcant positive result that has emerged from this line of enquiry is the
following:

� � � � � �

� � �

�

�

�

�

Theorem 4.50 If F is a ﬁrst-order deﬁnable class of frames, then �F is canonical.

Again, we prove this in Chapter 5 using algebraic tools (see Theorem 5.56). Tanta-
lizingly, at the time of writing the status of the converse was unknown: If a normal
modal logic � is canonical, then there is a ﬁrst-order deﬁnable class of frames F
�F. This conjecture seems plausible, but neither proof nor coun-
such that �
terexample has been found.

�

A third response has been to examine particular classes of normal modal log-
ics more closely. The entire lattice may have undesirable properties — but many
sub-regions are far better behaved. We will examine a particularly well-behaved
sub-region (namely, the normal logics extending S4.3) in the ﬁnal section of this
chapter.

This concludes our survey of basic completeness theory. The next four sections

218

4 Completeness

(all of which are on the basic track) explore the following issue: how are we to
prove completeness results when we need to build a model that has a property for
which no formula is canonical? Some readers may prefer to skip this for now and
go straight on to the following chapter. This discusses completeness, canonicity
and correspondence from an algebraic perspective.

Exercises for Section 4.4
4.4.1 Recall that any normal modal logic that has the ﬁnite model property also has the
ﬁnite frame property. What are the consequences of this for incomplete normal modal
logics?

� �

4.4.2 The logic KvB consists of all formulas valid on the general frame �. The domain �
of � is �
� �� (the set of natural numbers together with two further points), and �
is deﬁned by ��� iff �
is shown in Figure 6.2 in Chapter 6.) �, the collection of subsets of � admissible in �,
consists of all �
�.

� such that either � is ﬁnite and �

�, or � is co-ﬁnite and �

� � and � � � or �

�. (The frame �

� � and �

�� �

� � �

�

�

��

�

�

��

�

�

�

(a) Show that ��
(b) Show that on any frame on which the previous formula is valid, ��

� is valid on �.

��� �

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

��� �

�

���

is valid too.
(c) Show that ��
(d) Conclude that KvB is incomplete.

��� �

�

��� is not valid on �.

4.4.3 Consider the formulas (T) �

�

�

� and (Q) �
by these formulas.

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

�, (M) ��

�, (E) �
�. Let � denote the normal modal logic axiomatized

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

�

�

(a) Prove that � corresponds to the following ﬁrst-order formula: �

��

�

���

��

�

�

�

�

���

�

��

�

��

�

�

��

�

��

�

� � ��

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

���.

(b) Prove that within the class of frames validating both T and M, Q deﬁnes the frames
� (that is, if ��� then there is ﬁnite path back from

�

�

�

satisfying the condition �
� to �).

(c) Prove that the conjunction of the four axioms deﬁnes the class of frames with a

trivial accessibility relation — that is, � � � � � � � corresponds to �

��

���

�

�

�. (Hint: consider the effect of the McKinsey formula on the frames satisfying

�

�

�

the condition �

�

�.)

�

�

(d) Consider the so-called veiled recession frame �

�, where � is the set of natu-
ral numbers, ��� holds iff �
� � and � is the collection of ﬁnite and co-ﬁnite
subsets of �. Show that all four axioms are valid on this general frame, but that the
formula �

� can be refuted.

� �� �

�

�

�

�

�

(e) Conclude that � is incomplete, although it deﬁnes an elementary class of frames.
(f) Does this contradict Theorem 4.50?

4.4.4 Given a class � of frames, let �
and given a logic �, let ��

�

�

�

�

� �

�

� denote the set �

�

�

�

�

� for all � in �

�

� denote the class of frames on which � is valid.

(a) Show that the operations � and �� form a so-called Galois connection. That is,

prove that for all classes � and logics �:

�

�

�

�

� iff �

�

��

�

�

�

�

�

4.5 Transforming the Canonical Model

219

(b) What does it mean for a logic � if �

�

�

�

�

�

��

��? (Give an example of a logic for

which it does not hold.)

(c) What does it mean for a frame class � if �
frame class for which it does not hold.)

��

�

�

�

�

�

��? (Give an example of a

4.5 Transforming the Canonical Model

What is the modal logic of partial orders? And what is the tense logic of strict
total orders? Such questions bring us face to face with the fundamental problem
confronting semantically driven completeness results. Partial orders are antisym-
metric, and strict total orders are irreﬂexive. No modal formula deﬁnes either prop-
erty, and (as the reader probably suspects) no formula is canonical for them either.
Thus, to answer either question, we need to build a model for which we lack a
canonical formula — and hence we will need to expand our repertoire of model
building techniques. This is the main goal of the present section and the three that
follow.

In this section we explore a particularly natural strategy: transforming the canon-
ical model. Although a canonical model may lack some desired properties, it does
get a lot of things right. Perhaps it is possible to reshape it, transforming it into
a model with all the desired properties? We have done this once already, though
� (see Theorem 4.41 and
in a very simple way: in the completeness proof for K�
surrounding discussion) we formed a point-generated submodel of the canonical
model to ensure trichotomy. Here we will study two more sophisticated transfor-
mations — unraveling and bulldozing — and use them to answer the questions
with which this section began.

It seems plausible that S4 is the modal logic of partial orders: Theorem 4.29 tells
us that S4 is complete with respect to the class of reﬂexive transitive frames (that
is, preorders) and there don’t seem to be any modal formulas we could add to S4
to reﬂect antisymmetry. Furthermore, it seems reasonable to hope that we could
prove this using some sort of model transformation: as every S4-consistent set of
formulas can be satisﬁed on a preorder, and as we know that modal languages are
blind to antisymmetry (at least as far as frame deﬁnability is concerned) maybe we
can ﬁnd a way of transforming any satisfying preorder into a partial order without
affecting satisﬁability? (It’s worth stressing that this informal line of argument is
not a proof; it’s intended solely to motivate the work that follows.)

A transformation called unraveling will enable us do this. Indeed, unraveling
will let us prove the stronger result that S4 is complete with respect to the class of
reﬂexive and transitive trees. (This will be useful in Chapter 6 when we discuss
decidability). We brieﬂy discussed unraveling in Chapter 2, where we used it to
Informally,
show that modal logic has the tree property (see Proposition 2.15).
given any model, unraveling builds a new model, whose points are paths of the

220

4 Completeness

�

�

�

�

��

��

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

� �

�

��

�

�

��

�

�

��

�...

Fig. 4.1. A model and its unraveling

original model. That is, transition sequences in the original model are explicitly
represented as states in the unraveled model. More precisely:

Deﬁnition 4.51 (Unraveling) Let �
� . The unraveling of �

�� �

� around � is the frame �

�

�

� �

�

� where:

� be a frame generated by some point �

�

�� �

(i) �

� is the set of all ﬁnite sequences �
, and
� and ���

� � � � � ��

�

�

��

�

�

�� �

� � � � � �

� such that �

�

�

�

� � � � � �

�

�

(ii) If ��

� ��

�

� , then �

�

���

if there is some �

� such that ��

�

��

� �

� �

�

��

,

�

�

�

�

�

�

where + denotes sequence concatenation.

If �
then we deﬁne the valuation �

� is a model and �
� on �

�� �� �

� �

�

�

�

� �

�

�

� is the unraveling of �
� as follows:

� �

�

�� �

� around �,

�

�

�

�

�� �

� � � � � �

�

�

�

�

�

� � ��

� �

�

�

�

��

�

�

�

The model �

�

� �

� �

��

�

�

�

�

� is called the unraveling of � around �. �

A simple example is given in Figure 4.1. As this example suggests (and as the
reader should check) unraveling any frame around a generating point � yields an
irreﬂexive, intransitive, and asymmetric frame. Indeed, note that unraveled frames
are trees: the root node is the sequence �
� is just the familiar
(immediate) successor (or daughter-of) relation on trees.

�, and the relation �

�

Lemma 4.52 Let �
�. Then �
morphic image of �

�� �

�.

�

� �

� �

��

�

�

�

�

� be the unraveling of �

� is a bounded morphic image of �

�

�

� �

�

� around
�, and � is a bounded

�� �� �

� �

Proof. Let �
that � is surjective, has the back and forth property, and that for any ��

� be deﬁned by �

. It is easy to see
� , �� and

� � � � � �

�� �

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

� satisfy the same propositional variables. �

�

��

�

A simple corollary is that any satisﬁable set of formulas is satisﬁable on a (irreﬂex-
ive, intransitive, and asymmetric) tree: for if a set of formulas is satisﬁable, it is

4.5 Transforming the Canonical Model

221

satisﬁable on a point-generated model (take the submodel generated by the satis-
fying point), hence by unraveling we have the result. It follows that K is (strongly)
complete with respect to this class of models.

�

�

�

� �

But our real interest is S4. How do we use unraveling to make the partially or-
dered models we require for the completeness result? In the most obvious way
possible: we simply take the reﬂexive transitive closures of unraveled models.
More precisely, suppose we unravel � around some generating point � to obtain
� is the reﬂexive
� is a
� is an antisymmetric frame. Indeed, it is a reﬂexive and transitive
� is simply the familiar dominates (or ancestor-of) relation on trees. So
�? In general, no.

transitive closure of �
tree, �
tree, for �
only one question remains: is � a bounded morphic image of �
But if the model � we started with was itself reﬂexive and transitive, yes:

� is an S4 model. Moreover, as �

�. Now consider the model �

�. Trivially, �

� where �

� � �

� � �

� �

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

�

�

Lemma 4.53 Let �
some �
� , and let �
�, and deﬁne �
reﬂexive transitive closure of �
�.
bounded morphic image of �

� be the unraveling of � around �. Let �

� be a reﬂexive transitive model generated by
� be the
�. Then � is a

� to be �

�� �� �

� � �

� �

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

Proof. It is easy to see that the function � deﬁned in Lemma 4.52 remains the
required bounded morphism; as far as surjectivity, the back property, and the dis-
tribution of proposition letters are concerned, nothing has changed. We only have
� does not harm the forth
to check that taking the reﬂexive transitive closure of �
property. But, as � is itself reﬂexive and transitive, the forth property survives. �

Theorem 4.54 S4 is strongly complete with respect to the class of partially or-
dered reﬂexive and transitive trees.

Proof. If � is an S4-consistent set of formulas, and �
� is an S4-MCS extending
�, then �
�� is a
reﬂexive transitive model. We now transform this model into the required partial
order in two steps.

�. Moreover, as the S4 axioms are canonical, �

� �

��

�

�

Step 1. Let �

� be the submodel of �

�� generated by �

�. Clearly this is a

reﬂexive, transitive, point-generated model such that �

�

�

�

� �

�.

Step 2. Let �
of �

� around �

�.

�

�

�

�

� �

� � �

�

�

� be the reﬂexive transitive closure of the unraveling

� under � , hence for all
By Lemma 4.53, �
�, and by the surjectivity of � there is at
sequences ��
least one such ��. Hence we have satisﬁed � on a reﬂexive and transitive tree. �

� is a bounded morphic image of �
�, we have �

��

� ��

�

�

�

�

�

�

The previous proof could be summed up as follows: we found a way to use the in-
formation in a canonical model indirectly. The canonical model for S4 did not have

222

4 Completeness

the structure we wanted — nonetheless, we successfully tapped into the informa-
� as a bounded
tion it contained via a short sequence of bisimulations (�
morphic image, and �
� was a generated submodel of �

� had �
��).

Unraveling is an intrinsically global transformation that can change a model’s
geometry drastically. This is in sharp contrast to the transformation we will now ex-
amine — bulldozing — which works locally, and (in spite of its name) rather more
gently. We will use bulldozing to answer the second of the questions posed above.
Recall that a strict total order (STO) is a relation that is transitive, trichotomous
and irreﬂexive. The class of strict total orders contains such important structures as
� (the natural numbers, the integers, the rationals
and the reals in their usual order) and is widely used to model various temporal
phenomena. What is its tense logic?

�, and �

�, �

�, �

� �

� �

� �

� �

�

�

�

�

�

Once again, it is not hard to ﬁnd a plausible candidate: K�

�, the tense logic

�

�

�

�

and .3

, seems the only reasonable candidate. For a start, K�

generated by 4, .3
is strongly complete with respect to the class of weak total orders. (To see this,
observe that the axioms are canonical for transitivity and non-branching. Hence
� of the canonical model is transitive and tri-
any point generated submodel �
chotomous, and the completeness result is immediate.) Moreover, there simply are
no other plausible axioms — in particular, irreﬂexivity is not deﬁnable. Has this
(somewhat dangerous) line of reasoning led to the right answer? Let us see.

�

�

�

If we could ﬁnd a way of transforming weakly linear models into strictly linear
models we would have the desired completeness result. Note that unraveling won’t
help — it would turn the weak total order into a tree, thus destroying trichotomy.
If only we could ﬁnd a method which replaced the undesirable parts of the model
with some suitable STO, and left the good parts untouched: then trichotomy would
not be affected, and we would have assembled the required strict total order. Bull-
dozing is a way of doing this. The ﬁrst step is to pin down what the ‘undesirable’
parts of weak total orders are. The obvious response is ‘reﬂexive points’ — but
while this isn’t exactly wrong, it misses the crucial insight. The entities we really
need to think about are clusters, introduced in Chapter 2. We repeat the deﬁnition:

� � �

� be a transitive frame. A cluster on �

� is a subset
Deﬁnition 4.55 Let �
� of � that is a maximal equivalence relation under �. That is, the restriction of
� to � is an equivalence relation, and this is not the case for any other subset �
�. A cluster is simple if it consists of a single reﬂexive point,
of � such that �
and proper if it contains more than one point. When we say that a model contains
clusters, we mean that its underlying frame does. �

� � �

�

The point is this: we should not think in terms of removing isolated reﬂexive points;
rather, we should remove entire clusters at one stroke. (Intuitively, the information
in a cluster is information that ‘belongs together’.) Any transitive trichotomous

4.5 Transforming the Canonical Model

223

frame can be thought of as a strictly totally ordered collection of clusters (cf. Exer-
cise 1.1.1). If we could remove each cluster as a single chunk, and replace it with
something equivalent, we would have performed a local model transformation.

So the key question is: what should we replace clusters with? Clearly some sort
of STO — but how can we do this in a truth preserving way? Note that any cluster
�, even a simple one, introduces an inﬁnity of information recurrence in both the
forward and backward directions: we can follow paths within �, moving forwards
and backwards, for as long as we please. Thus, when we replace a cluster � with a
STO, we must ensure that the STO duplicates all the information in � inﬁnitely of-
ten, in both directions. Bulldozing does precisely this in a straightforward way. We
simply impose a strict total order on the cluster (that is, we pick some path through
the cluster that visits each point once and only once) and then lay out inﬁnitely
many copies of this path in both the forward and backward direction. We then re-
place the cluster by the inﬁnite repetition of the chosen path. We have squashed
the clusters down into inﬁnitely long STOs — hence the name ‘bulldozing’.

Theorem 4.56 K�4.3 is strongly complete with respect to the class of strict total
orders.

�

�. Let �

Proof. Let � be a K�4.3-consistent set of formulas; expand it to a K�4.3-MCS
� be the canonical model for K�4.3. By the canonicity
� be the
� is a transitive and trichotomous model such

of the axioms, � is transitive and non-branching. Let �
submodel of � generated by �
that �

� may contain clusters, which we will bulldoze away.

�. But �

�; �

� � �� �

�� �

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

Index the clusters in �

Step 1.
Step 2. Deﬁne an arbitrary strict total order �
Step 3. Deﬁne �
to be �
Step 4. Deﬁne �, the set underlying the bulldozed model, to be �

�. (� is the set of integers.)

� by some suitable set �.

� on each cluster �

.

�

�

�

�

�

�

�

�

�

,

�

�

�

�

where �

� is the set �
Step 5. Deﬁne a mapping �

�

�

�

�

�

�

�

�

�

�

�

� of points not belonging to any cluster.
�, if

�; and �

�, if �

� �

� �

�

�

�

�

�

�

�

� by: �

�

�� �

� �

�.

Step 6. Deﬁne an ordering �

� on � by � �

�

� iff

�

either (�
or �

� �

�

�

� or �
� and �

�

�� �

�

� �

�) and �
� and

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

�;

either � and �
or � and �

� belong to distinct clusters and �
� belong to the same cluster and � �

�

�

�

�

�

�

�

�

�

�;

� (where �

� is

�

�

the usual ordering on the integers);
� belong to the same cluster �

�

or � and �

and �

� and � �

�

�.

�

�

�

Step 7. Deﬁne a valuation �
Step 8. Deﬁne �

�, the bulldozed model, to be �

� � �

� iff �
�.

� �

�

�

�

� on �

�

� by �

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

�.

�

224

4 Completeness

We now make the following claims:

Claim 1. The mapping � is a surjective bounded morphism from �
� under �.

� is a bounded morphic image of �

�, and the model �

�� �

�

�

�

� to

� � �

Claim 2. �

�

� � �

� is a strict total order.

Proving these claims is a matter of checking the deﬁnitions; we leave this to the
reader as Exercise 4.5.5. With this done, the theorem is immediate. By Claim 1,
�, and since � is surjective, there is at
for any �
least one such �. Thus � is a model of �, and by Claim 2 it has the structure we
want. �

� we have �

��

� �

�

�

�

�

�

�

�

Although it works more locally, like unraveling, bulldozing is a way of using the
information in canonical models indirectly.
Indeed, like unraveling, it accesses
the information in the relevant canonical model via a sequence of bisimulations:
� in turn was a
� had �
the ﬁnal model �
generated submodel of �.

� as a bounded morphic image, and �

�

�

Bulldozing is a ﬂexible method. For example, we’re not forced to deﬁne �

to
�; any unbounded STO would do. Moreover, if we used a reﬂexive total
be �
��) instead, we could prove analogous completeness results
order (for example �
for reﬂexive total orders; for example, the reader is asked to show in Exercise 4.5.6
� is the logic of this class of frames. Moreover, for modal languages,
that S�
we only need to ensure inﬁnite information repetition in the forward direction, so
structures such as �

�� sufﬁce.

� and �

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

But there are more interesting variations. For example, instead of simply order-
ing the points in the cluster, one can embed the cluster in some suitable total order,
and work with its embedded image instead. By embedding the clusters in a dense
set, it is possible to build dense totally order ordered models. And by combining
such ideas with other transformations (notably ﬁltrations) the method can be used
to prove many classic completeness results of modal and tense logics.

Model manipulation methods, and completeness proofs making use of them,
abound. Further examples are mentioned in the Notes, but it is not remotely possi-
ble to be encyclopedic: such methods trade on speciﬁc insights into the geometry
of relational structures, and this gives rise to a wide variety of variants and com-
binations. The reader should certainly be familiar with such methods — they are
often simple to adapt to speciﬁc problems — but it is just as important to appreci-
ate the general point that has emerged from our discussion: even if the canonical
model is not quite what we need, it can still be extremely useful. The following
section further explores this theme.

Exercises for Section 4.5
4.5.1 K is complete with respect to the class of irreﬂexive frames. Unraveling shows this,

4.6 Step-by-step

225

but there is a much simpler transformation proof. (Hint: given a model �, tinker with the
disjoint union of � with itself.)

4.5.2 Formulate the unraveling method for modal languages containing two diamonds.
Then formulate the method in such a way that bidirectional frames unravel into bidirec-
tional frames.

4.5.3 Consider a similarity type � with one binary operator �. Call a � -frame �
acyclic if the binary relation �
� ��� or � ��� for some �
acyclic (that is to say, �
sound and complete with respect to the class of acyclic frames.

� is irreﬂexive). Prove that the basic modal logic �

� ��

� �

�� �

�

�

�

�

� �

�

�� �

� is
is strongly

�

�

4.5.4 Show that the canonical model for �

�

� contains proper clusters.

4.5.5 Prove Claims � and � of Theorem 4.56.

4.5.6 Let K �QT be the smallest normal temporal logic containing both K �Q and �
� �.
Show, using a light bulldozing argument, that K �QT is strongly complete with respect to
the class of all dense unbounded reﬂexive total orders.

�

4.6 Step-by-step
Three main ideas underly the step-by-step method:

(i) Don’t consider the entire canonical model to be the key ingredient of a
completeness proof. Rather, think of selections of MCSs from the canonical
model as the basic building blocks.

(ii) The standard way of proving completeness is by constructing a model for
a consistent set of formulas. Take the term ‘constructing’ as literally as
possible: break it down into a sequence of steps.

(iii) Putting the ﬁrst two observations together, think of the construction of a
model as the stepwise selection of the needed MCSs. More precisely, think
of the model construction process as approaching a limit via a sequence
of ever better approximations, using local conﬁgurations of the canonical
model to make improvements at each step of the construction.

The method gives us enormous control over the models we build, and even at this
stage it’s easy to see why. First, we do not have to worry about unpleasant features
of the canonical model (such as clusters) since we only work with selections of
the information that canonical structures contain. Furthermore, as we select our
information one step at a time, we obtain an iron grip on what ends up in the
model.

To illustrate the method’s potential, we use it to prove that the logic �

� de-
�. In what fol-
ﬁned in Deﬁnition 4.40 is strongly complete with respect to �
� is this logic’s
lows, consistency means �
canonical model. Furthermore we ﬁx a maximal consistent set �; the goal of our

�-consistency, and �

�� �

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

226

4 Completeness

� is an ordering
proof is to construct a model �
�. At each step of the construction we will be dealing
which is isomorphic to �
with an approximation of � consisting of a strictly ordered ﬁnite set of points (that
will ultimately end up) in � and for each of these, the set of all formulas that we
want to be the point’s modal type (that is, the set of formulas holding at the point).

� for � such that �

� � �� �

� � �

� �

� �

�

Deﬁnition 4.57 A network is a triple � � �
� such that � is a binary re-
lation on the set � , and � is a labeling function mapping each point in � to a
maximal consistent set. �

� � �� �

We are not interested in networks that are blatantly faulty as approximations of our
desired model. For example, we want � to be a strict total ordering. Moreover,
whenever a formula � is in the label set of a point �, then � � should be in �
� for
any � with ���. Such requirements lead to the following deﬁnition.

�

�

Deﬁnition 4.58 A network � � �

� � �� �

� is coherent if it satisﬁes:

(C1) � is a strict total ordering,
(C2) �

� for all �� �

�

�

�

�

�

�

�

�

�

� such that � � �.

A network for � is a network such that � is the label set of some node. �

C1 and C2 are the minimal requirements for a network to be useful to us; note that
both requirements are universal. (C2 is equivalent to the requirement that if � � �
then � �
�.) But if a network
is to really resemble a model, it must also satisfy certain existential requirements.

� for all �

� for all �

� and � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

Deﬁnition 4.59 A network � � �

� � �� �

� is saturated if it satisﬁes:

(S1) � is unbounded to the left and to the right,
(S2) � is dense,
(S3) � is modally saturated. That is, we demand that (F) if � �

� , then there is some �
� for some �

�

�

�

�

�

�

� �

� such that ��� and �

�

� , then there is some �

�

�

�

�

�

�

� for some
�, and (P) if
� such that ��� and

�

�

�

�

�

�

�

�

�.

�

A network is perfect if it is both coherent and saturated. �

We want networks to give rise to models. Let’s now check that we have imposed
sufﬁciently many criteria on networks to achieve this.

Deﬁnition 4.60 Let � � �
underlying frame of � . The induced valuation �

� � �� �

�

�

�

�

�

�

�

�

�

��. The structure �

�

� �

�

� �

�

�

�

�

on � is deﬁned by �
� is the induced model. �

�

�

�

� �

� be a network. The frame �

� �

� � �

� the

�

The following lemma shows that our deﬁnition of perfection is the right one.

4.6 Step-by-step

227

Lemma 4.61 (Truth Lemma) Let � be a countably inﬁnite perfect network. Then
for all formulas �, and all nodes � in � ,

�

� �

�

�

� iff �

�

�

�

�

�

�

Moreover, �

is isomorphic to the ordering of the rational numbers.

�

Proof. The ﬁrst part of the proof is by induction on the degree of �. The base case
is clear from the deﬁnition of the induced valuation, and the steps for the booleans
are straightforward. As for the modal operators, the coherency of � drives the left
to right implication through, and saturation takes care of the other direction.

Finally, the underlying frame of a perfect network must be a dense, unbounded,
strict total ordering. Hence, if it is countably inﬁnite, it must be isomorphic to
� by Cantor’s Theorem. (Readers unfamiliar with this theorem should try
to prove this classic result from ﬁrst principles. The standard proof builds up the
isomorphism using a step-by-step argument!) �

� �

�

�

It follows from Lemma 4.61 that we have reduced the task of ﬁnding a model for
� to the quest for a countable, perfect network for �. And now we arrive
our MCS
at the heart of the step-by-step method:
the crucial idea is that each witness to
the imperfection of a coherent network can be removed, one step at a time. Such
witnesses will be called defects. There are three kinds of defect: each corresponds
to a violation of a saturation condition.

�

� � �� �

� be a network. An S1-defect of � consists of

� that has no successor, or no predecessor; an S2-defect is a pair �

Deﬁnition 4.62 Let � � �
a node �
of nodes for which there is no intermediate point. An S3-defect consists of (F) a
� for which there is no � in � such that ��� and
node � and a formula � �
� for which there is no � in �

�, or (P) a node � and a formula � �

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

�

�

�

such that ��� and �

�. �

�

�

�

�

Now we need to say more what it to repair a defect. To make this precise, we need
the notion of one network extending another.

Deﬁnition 4.63 Let �
� is a subframe of �

�

�

and �
� and �

�

be two networks. We say that �
on �
agrees with �

. �

�

extends �

�

if

�

�

�

�

�

The key lemma of this (or for that matter, any) step-by-step proof states that any
defect of a ﬁnite coherent network can be repaired. More precisely:

Lemma 4.64 (Repair Lemma) For any defect of a ﬁnite, coherent network �
� lacking this defect.
there is a ﬁnite, coherent �

�

�

228

4 Completeness

Proof. Let � � �
� be a ﬁnite, coherent network and assume that � has
some defect. We prove the Lemma by showing that all three types of defect can be
removed.

� � �� �

S1-defects.
These are left as an exercise to the reader.

How should we repair this defect? The basic idea is simple:

S2-defects.
Assume that there are nodes � and � in � for which there is no intermediate point.
just throw in a
new point between � and �, and ﬁnd an appropriate label for it. This can be done
�, and by canonicity of
easily, since it follows by coherence of � that �
�. Hence,
the density axiom that there is some MCS
take some new node � (new in the sense that �
by

� ) and deﬁne �

� such that �

� �

� �

� �

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

�

�

�

�

�

�

�

�

�

�

�

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

� �

�

�

�

�

�� �

�

�

�� �

�

�

�

��

� ��

� �

�

� � ��

� �

�

�

�

�

�

�� �

�

��

� ��

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

� such that � �

It is clear that �
� is a network that does not suffer from the old defect. But is �
coherent? Condition C1 is almost immediate by the deﬁnition, so we concentrate
on C2. Let � and � be two arbitrary nodes in �
�; we have to check
� is irreﬂexive, � and � are distinct. Moreover, there
�. Now, as �
that �
can only be a problem if one of the nodes is the new point �; assume that �
� by our assumption
(the other case is similar). If �
on � , so suppose that �
� and the fact that there are no old
nodes between � and �, this means that � � �, so by the coherency of � we have
� ; but then
that �
it is immediate by the deﬁnition of �

�. Hence, it follows by the transitivity of �

�. By deﬁnition of �

� then we have �

� that �

� that �

�.

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

S3-defects.
We only treat the P-defects; the case for F-defects follows by symmetry. Assume
that there is a node � in � and a formula � � in �
� for which there is no � in �
such that � � � and �

�.

�

�

�

�

�

�

Again, the basic strategy is simple: we insert a new point �

� into the network
(before �!) and choose an adequate label for it; this has to be a maximal consistent
set containing � and preceding �
� be
inserted? If we are not careful we will destroy the coherency of � . The following
is a ﬁnite STO) overcomes
maneuver (which takes advantage of the fact that �
the difﬁculty.

�. But where should �

� in the preorder �

�

�

�

Let � be the unique point in � such that (1) �

� is an S3-defect in � , and
� is not a defect. Such an � must exist (it is either �

�� � �

(2) for all � � �, �

�� � �

4.6 Step-by-step

229

�� � �

itself, or one of the ﬁnitely many points preceding �) and, as we will see, we can
� immediately
� without problems by simply inserting the new point �
repair �
before �. Repairing this minimal defect automatically repairs the defect �
�.
�) and let � be an MCS containing �
�; such a � exists by the Existence Lemma for normal logics.

Choose some new point �

� (that is, �

�� � �

�

��

�

�

�

�

such that � �
Deﬁne �

�

� �

�

�

�

�

� �

� �

� as follows.

�

�

�

�

�

��

� �

�

�

�

�

�

�

�� �

� � �

�

� �

�

�

��

� ��

� �

� � ��

� �

�

�

�

�

�

�

�

� �

��

� ��

��

Observe that �

�

� is a strict total order, and that �

�. It only remains to ensure that �

�

�� � �

Consider two nodes �� �

�

�

� such that � �

� does not contain the defect
� satisﬁes the second coherency condition.
�. Again, the only cases worth
� we are in a
�. If we have �

�

�

checking are when either � or � is the new point �
similar situation as in the case of S2-defects, so we do not go into details here.

�

Hence, assume that �

�

coherency of � , �
relation with no branching to the left — hence either � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

� . We claim that the ﬁrst two options are impossible. For, if � �

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

�. By construction �
�. But �

� is the canonical relation for �

�, and by the
� — a
� or
� then
� and this contradicts the minimality of �; and
� was not a defect in the ﬁrst

�, �

�� � �

�

�

�

�

�

�

�

�

�

�

�

�

�

� would mean that �

�

�

�

�

�

�

�

�

�

� , which establishes coherence. �

�

�

� would imply that � �
�, then �

if �
place! We conclude that �

�

�

�

�

�

�

�

�

With both the Truth Lemma for Induced Models and the Repair Lemma at our
disposal, we can prove the desired strong completeness result. The idea is straight-
forward. We start with a singleton network and extend it step-by-step to larger
(but ﬁnite) networks by repeated use of the Repair Lemma. We obtain the required
perfect network by taking the union of our sequence of networks.

Theorem 4.65 �

�

� is strongly complete with respect to �

�

�.

� �

� �

Proof. Choose some set �
� (we will use its elements to build the
required frame) and enumerate the set of potential defects (that is, the union of the
sets �, �
����). Given a consistent set of formulas �,
� and �
expand it to an MCS
is a ﬁnite, coherent network for �

be the network ��

��. Trivially, �

. Let �

.

� � �

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

�

�

Let �

� � and suppose �

is a ﬁnite, coherent network. Let � be the defect of
that is minimal in our enumeration. Such a � exists, since any ﬁnite network
by repairing the defect � as
must at least have S1- and S2-defects. Form �
described in the proof of the Repair Lemma. Observe that � will not be a defect
of any network extending �

.

��

�

�

230

4 Completeness

Let � � �

� � �� �

� be given by

�

�

� �

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

�

�

�

�

�

�

�

�

�

�

�

�

It is easy to see that �
� from a countably inﬁnite set, � is countable.

�

is a strict total order. Moreover, as we chose the points in

It should be intuitively clear that � is perfect, but the actual proof has to take
care of a subtlety. Suppose that � is not perfect; let � be the minimal (according
to our enumeration) defect of � , say �
. By our construction, there must
of � of which � is also a defect. Note that � need not
be an approximation �
— this is the subtlety. Fortunately, there can be at
be the minimal defect of �
most � defects that are more urgent, so � will be repaired before stage �
� of the
construction.

�

�

�

�

�

�

Finally, by the perfection of � it follows from Lemma 4.61 that the induced

model �

satisﬁes � at �

. �

�

�

The step-by-step method is one of the most versatile tools at the modal logician’s
disposal: a wide variety of results in modal and tense logic have been using this
method, it is the tool of choice for many stronger modal systems such as Arrow
Logic and Since-Until logic, and we will make use of step-by-step arguments when
we discuss rules for the undeﬁnable in the following section. We urge the reader to
experiment with it. A good starting point is Exercise 4.6.1.

Exercises for Section 4.6
4.6.1 Consider a modal language with three diamonds �
axiomatization for the class of frames �

�� �

� �

� �

� �

�

and �

, �
� satisfying �

�

�

. Give a complete

�

�

�

�

.

�

�

�

�

�

�

��

4.6.2 Consider, for a modal language with two diamonds �
logic �

, the normal modal
� axiomatized by S5 axioms for both diamonds, and the commutativity axiom
�. Prove that this logic is complete for the class of square frames. A
� where for some set � we

and �

�

�

�

�

�

�� �

� �

square frame for this language is of the form �
have

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

��

iff

�

�

�

�

�

�

�

Hint: take as approximations networks of the form �
pairs over � to maximal consistent sets.

� where � is a labeling mapping

� � �

4.6.3 Consider a similarity type � with one binary operator �, as in arrow logic. Call a
� a relativized square if � is some collection of pairs over a base set
� -frame �
and �
� , and �

� satisﬁes � ��� iff �

, �

.

�� �

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

(a) Prove that the basic modal logic �
the class of relativized squares.

�

is strongly sound and complete with respect to

(b) Try to axiomatize the logic of the class of frames �

�� �

� in which � is as above,

but � satisﬁes � ��� iff �

, �

� and �

�

�

�

.

�

�

�

�

�

�

�

4.7 Rules for the Undeﬁnable

231

4.7 Rules for the Undeﬁnable
In the previous two sections we proved semantically driven completeness results
by using standard canonical models indirectly. The present section takes a rather
different approach: we enrich the deductive system with a special proof rule, and
consider a special (not necessarily generated) submodel of the canonical model for
this new logic. The submodel that we study contains only special distinguishing (or
witnessing) MCSs. The completeness proof shows that this new canonical model
has all the good properties of the original, and that, in addition, it is already in
the right shape. We will make use of ideas introduced in our discussion of the
step-by-step method in the previous section (in particular, the concept of a defect).
The running example in this section will (again) be the tense logic of dense un-
bounded strict total orderings. Recall that the difﬁculty when working with this
logic is that there is no axiom ensuring the irreﬂexivity of the canonical frame —
we have all the other required properties: point generated submodels of the can-
� are transitive, trichotomous, dense, and unbounded. Now, in
didate logic �
previous sections we achieved irreﬂexivity indirectly: either we bulldozed away
� to induce a model on a care-
clusters, or we used the canonical model for �
fully constructed irreﬂexive frame. In this section we will construct a canonical
frame that is transitive, non-branching, dense and irreﬂexive right from the start.
Indeed, if we work with a countably inﬁnite language, every point generated sub-
frame of this canonical model will be countable, and hence (by Cantor’s Theorem)
isomorphic to �

�.

� �

�

�

�

The starting point of the enterprise is that irreﬂexivity, although not deﬁnable in

basic modal languages, can be characterized in an alternative sense:

If a temporal formula � is satisﬁable on an irreﬂexive frame, then for any
proposition letter � not occurring in �, the conjunction ��
is also satisﬁable on that frame.

� �

� �

� �

� �

�

�

�

�

� � � �

�, then �

� is just like �
For, if �
� to �. The condition that � does not occur in
except that it assigns the singleton �
� is crucial here: it ensures that changing the set assigned to � does not affect the
satisfaction of �.

�, where �

� �

� �

� �

� �

��

� �

� �

�

�

�

�

�

Now, by taking the contrapositive of the above statement, we turn it into a proof

rule:

(IRR)

if � ��

� �

�

� �

�

� �

� �

� then �

�, provided � does not occur in �.

We have just seen that this rule is sound on the class of irreﬂexive frames. More-
� is
over, note that on the class of strict total orders the formula ��
true at some state � iff � is the only state where � holds (we need trichotomy and
� � acts as a sort of
transitivity to guarantee this). That is, the formula �
�. Bearing these remarks
‘name’ for the satisfying point. Call this formula ����

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

232

4 Completeness

in mind, let us now see how adding this rule is of any help in proving the desired
completeness result.

Deﬁnition 4.66 The logic �
rule IRR. In what follows, consistency means �
� is provable in �

�

�

�

�, and so on. The canonical model for �

� is obtained by adding to �

�

�-consistency, �

�

�

� the irreﬂexivity
� means that
� is denoted by

�

�, the canonical relation by �

�. �

�

�

�

�

�

� with respect to �

The remainder of this section is devoted to proving completeness of the proof sys-
�. Of course the result is not surprising: we have
tem �
�. It
already seen that plain old �
is the method that is important: rules such as IRR give us a way of forming more
cleanly structured canonical models.

� is strongly complete with respect to �

� �

� �

�

�

�

Our goal is to construct an irreﬂexive version of the canonical model for �

�.

�

�

The basic idea is to work only with special witnessing MCSs:

Deﬁnition 4.67 A maximal consistent model is called witnessing if it contains a
formula of the form ����

�. �

�

�

Why are these witnessing MCSs so interesting? Well, suppose that we are dealing
with a collection � of witnessing maximal consistent sets. This collection induces
a model in the obvious way: the relation is just the canonical accessibility relation
restricted to � and likewise for the valuation. Now suppose that we can prove a
Truth Lemma for this model; that is, suppose we can show that ‘truth and mem-
bership coincide’ for formulas and MCSs. It is then immediate that the underlying
relation of the model is irreﬂexive: ����

� implies �

� and � �

� .

� �

�

��

�

�

This is all very well, but it is obvious that we cannot just throw away non-
witnessing MCSs from the canonical model without paying a price. How can we
be sure that we did not throw away too many MCSs? An examination of the stan-
dard canonical completeness proof reveals that there are two spots where claims
are made concerning the existence of certain MCSs.

�

�

�. But if � is witnessing, then there is some � with ����

(i) There is the Existence Lemma, which is needed to prove the Truth Lemma.
In our case, whenever the formula � � is an element of one of our witness-
ing MCSs (� , say) then there must be a witnessing � such that � �
� and
�;
it follows from the deﬁnition of the canonical accessibility relation that
� . This shows that it will not do to just take the
witnessing MCSs: the Existence Lemma requires stronger saturation condi-
tions on MCSs, namely that whenever � �
� , then there is some � such
that �

� too.

����

����

�� �

�� �

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

(ii) If there are axioms in the logic that are canonical for some property with

4.7 Rules for the Undeﬁnable

233

existential import, how can we make sure that the trimmed down version
of the canonical model still validates these properties? Examples are the
�, or, in the present case, the density axiom. The
formulas ��
point is that from the density of the standard canonical frame we may not
infer that its subframe formed by witnessing MCSs is dense as well: why
should there be a witnessing MCS between two witnessing MCSs?

��

�

�

These two kinds of problems will be taken care of in two different ways. We ﬁrst
deal with the Existence Lemma. To start with, let us see how sets of MCSs give
rise to models — the alternative versions of the canonical model that we already
mentioned.

Deﬁnition 4.68 Let � be a set of maximal consistent sets of formulas. Deﬁne
to be the submodel of the canonical model induced by � ; that is, �

�

�

�

�

�

�

�

�

�

�� �� �

� where � is the relation �

� restricted to � , and � is the canonical

relation restricted to � . �

Obviously, we are only interested in such models for which we can prove a Truth
Lemma. The following deﬁnition gives a sufﬁcient condition for that.

Deﬁnition 4.69 A set � of maximal consistent sets is called diamond saturated if
� there
it satisﬁes the requirement that for each �
� , and the analogous condition holds for
� such that ��
is a set �
past formulas. �

� and each formula � �

� and �

�

�

�

�

�

Lemma 4.70 (Truth Lemma) Let � be a diamond saturated set of maximal con-
sistent sets of formulas. Then for any �

� and any formula �:

�

�

�

� �

�

�

� iff �

�

�

� �

Proof. Straightforward by a induction on �. �

Our goal is now to prove the existence of diamond saturated collections of witness-
ing MCSs.

Proposition 4.71 Let � be some consistent formula. Then there is a countable,
� for some
diamond saturated collection � of witnessing MCSs such that �

�

� .

�

�

Proof. The basic idea of the proof is to deﬁne � step-by-step, in a sort of parallel
Lindenbaum construction on graphs. During the construction we are dealing with
ﬁnite approximations of � . At each stage, one of the shortcomings of the current
approximation is taken care of; this can be done in such a way that the limit of the
construction has no shortcomings at all. A ﬁnite approximation of � will consist

234

4 Completeness

�

of a ﬁnite graph together with a labeling which assigns a ﬁnite set of formulas to
each node of the graph. We associate a formula with each of these ﬁnite labeled
graphs, and require that this corresponding formula be consistent for each of the
approximations. The ﬁrst graph has no edges, and just one point of which the label
�. The construction is such that the graph is growing in two
set is the singleton �
senses: edges may be added to the graph, and formulas may be added to the label
sets. (Some readers may ﬁnd it helpful to think of this process as a rather abstract
tableau construction.) All this is done to ensure that in the limit we are dealing
with a (possibly inﬁnite) labeled graph meeting the requirements that (1) the label
set of each point is a MCS, (2) each label set contains a witness and (3) if a formula
of the form � � (� �) belongs to the label set of some node, then there is an edge
connecting this node to another one containing � in its label set. Finally, � is
deﬁned as the range of this inﬁnite labeling function — note that the label function
will not be required to be injective.

Now for the technical details. Approximations to � will be called networks: a
� is a ﬁnite, undirected,
� of
�; and � is a label function mapping each

network is a quadruple � � �
connected and acyclic graph; � is a direction function mapping each edge �
the graph to either � or its converse �
node of � to a ﬁnite set of formulas.

� such that �

� � � � �� �

� � �

�� �

As in our earlier example of a step-by-step construction, we ﬁrst want to formu-
late coherence conditions on networks and deﬁne the notion of a defect of network
with respect to its ideal, � . We start with a formulation of the coherence of a
network. Since we are working in the basic temporal similarity type — that is,
� — there is an obvious
we have diamonds both for looking along � and along �
� be
way of describing the network, from each of its nodes. Let � � �
some network, and let � and � be two adjacent nodes of � . We use the following
notational conventions:

� � � � �� �

� if �
� if �

�

� �

�� �

��

�

� �

�� �

�

�

�

�

� ��

��

�

� denote the set of nodes adjacent to �. Finally, we let �

� denote the

�

�

and let �
conjunction

�

�

�. Deﬁne

�

�

�

�

�

� �

�

�

��

�

� � � �

�

��

�

��

�

� �

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

� �� �

�

�

��

�

� � � �

�

�

��

�

��

�

� �

�

�

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

� �

��

� starts with a local description �

In words, �
neighbors. For each neighbor �, �
�) and then starts to describe the network after �
(and a past operator if �
by calling �. �
� of �, and then recursively
proceeds to the neighbors of � — except for �. The omission of �, together with the
ﬁniteness and acyclicity of the graph, ensures that we end up with a ﬁnite formula.

� ﬁrst gives a local description �

� writes a future operator if �

� of � and then proceeds to its

� � � �

� �

� �

�� �

�� �

��

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

4.7 Rules for the Undeﬁnable

235

The following claim shows that it does not really matter from which perspective

we describe � .

Lemma 4.72 For any network � and any two nodes �� � in � , �
tent iff �

� is consistent.

��

� �

� is consis-

� �

��

Proof. By the connectedness of � it is sufﬁcient to prove the Lemma for adjacent
� and �; the general case can be proved by a simple induction on the length of the
path connecting the two nodes.

So suppose that � and � are adjacent; without loss of generality assume that
�. Since � is ﬁxed it will not lead to confusion if we abbreviate �

� �

��

� �

�

�� �

�

�

by �

�

�

� and �

��

� �� �

� by �

�

�� �

�. Then by deﬁnition, �

�

� is given by

�

�

�

�

�

��

�

�� �

�

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

� �

�

� �

�

�

�

�

�

�

� �

�� �

��

�

�� �

�

�

� �

�

�

� �

�� �

�

�� �

�

�

Likewise, we can show that

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

�� �

� �

�� �

�

�

� �

�

� �

�

�

But it is a general property of any logic extending K�
� and �, � �
immediate. �

� is consistent iff �

that for any two formulas
� � is consistent. From this, the Lemma is

�

�

The upshot of Lemma 4.72 is a good deﬁnition of the coherence of a network: we
will call a network � coherent if �
� is consistent for each of (equivalently:
some of) its nodes �. However, being ﬁnite, our networks will never be perfect.
What kinds of defects can they have?

��

� �

A defect of a network is either (D1) a pair �
� such that � �

�; (D2) a pair �

�� � �

� such that neither � nor �

�

�� �

� for some node � with � �� and �

�

�

�

�

�

�

�

�

� while there is no witness
�); (D3)

� �

�� �

�

�; or (D4) a node � without a name; that is, ����

�

� �

�

�

�

�

�

�

�

belongs to �
for this (in the sense that �
a similar pair �
for no formula �.

�� � �

We will show that each kind of defect of a network can be repaired. For this we
�, while

� extends a network � , if �

�

�

need some terminology. A network �
� , �

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

� �

�

�

�

�

� for each node � of � .

�

Lemma 4.73 For any defect of a ﬁnite, coherent network � there is a ﬁnite, co-
herent �

� lacking this defect.

�

�

236

4 Completeness

Proof. Let � � �
� be a coherent network and assume that � has some
defect. We will prove the Lemma by showing how to remove the various types of
defect.

� � � � �� �

D1-defects.
Assume that there is a node � and a formula � such that neither � nor �
� is consistent, it follows that either �
to �. Since the formula �
� denote the formula such that �
or �
�, while �
�, �
is consistent. Now deﬁne �
� and
� for �

� is consistent; let �

� by �

� , �

� � �

� �

��

��

��

��

��

� �

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

� belongs

��

� �

�

� �

��

� �

�

� � �

� is given by

�

�

�

�

�

�

�

� ��

�

� � ��

�

Clearly, �

� is a ﬁnite network lacking the defect �

� �

� �

� � �

�, so �

�

��

�� �

�. It is also obvious that
� is consistent, and hence, �

�

�

�

� �

��

� is the formula �

��

is coherent.

D2-defects.
Assume that there is a node � and a formula � such that � �
� while there is
no witness for this. Take a new node � (that is, � does not belong to � ) and deﬁne

�

�

�

�

� as follows.

�

�

�

�

�

�

��

� �

�

�

�

�

�� �

�

��

� ��

��

�

�

�

�� �

� �

�

��

� ���

�

��

�

�

�

��

�

�

��

� ��

�

���

� extends � and that the defect has been repaired. Finally,
It is obvious that �
�: the only information that
it is clear by the deﬁnitions that �
the new node adds to the description is a conjunct � � and by assumption this was
�. Hence, the coherence of
already a member of �

�, and thus a conjunct of �

� �

��

��

� �

� �

�

�

�

�

�

�

� is an immediate consequence of the coherence of � .

�

D3-defects.
Repaired analogously to D2-defects.

D4-defects.
These are repaired in the same way as D1-defects, using the fact that if �
is consistent, then there is a propositional variable � that does not occur in any of
the label sets. And here — at last — we use the IRR-rule to show that the formula

��

� �

�

�

� �

�

��

� �

�

����

� is consistent. �

Finally, we return to the proof of Proposition 4.71. Assume that � is a consistent
formula.

By a standard step-by-step construction we can deﬁne a sequence ��

�

� of

�

�

�

networks such that

4.7 Rules for the Undeﬁnable

237

�

is a one-node network with label set �
whenever � � �,
extends �

(i) �
(ii) �
(iii) For every defect of any network �

�

�

�,

�

there is a network �

with � � � lacking

this defect.

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

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

� , �

� , deﬁne �

� belongs to �

; if neither � nor �

Let � be the set
that for every �
�, either � or �
�. Let �
� belongs to �
in �
by the construction there is some � � � such that either � or �
But then the same formula belongs to �
that every set �
there are formulas �
construction, there must be a �
But this contradicts the consistency of �

; and for �
�. We claim
� is a witnessing MCS. We ﬁrst show that for all formulas
� be such that � is already in existence
. Hence,
�.
�. In the same manner we can prove
� is not consistent; then
is inconsistent. By
�.
.

� contains a name. Now assume that �

� and hence, the coherency of �

�, this constitutes a defect of �

belongs already to �

� such that each �

� belongs to �

� such that �

, . . . , �

in �

� � � � �

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

Finally, deﬁne � as the range of �. The preceding paragraphs show that � is
, it follows that � belongs

a collection of witnessing MCSs. By our deﬁnition of �
to some MCS in � .

�

�

�

Now let � � be some formula in �

�

� . By deﬁnition, there is some �

that �
there is some �

�

�

�

�

�, and thus, some �

�

� and some �

�

�

�

� such that � �
such that �

�

�

�

�, so it remains to prove that �
suppose otherwise. Then there is a formula �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

� is a MCS, this implies that �
� and �

that �
inconsistent; this contradicts the coherency of �
saturated.

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

�

�

�� and �

� such
�. By our construction
�. It follows that
�. In order to reach a contradiction,
�. Since
� be large enough
� is
. This proves that � is diamond

� such that � �

��

� �

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

�. Now let �
�. From this it is immediate that �

�

But then we have prove that � meets all requirements phrased in the Proposi-

tion. �

This shows that we have more or less solved the ﬁrst problem concerned with work-
ing in a trimmed down version of the canonical model: we have established that
every consistent formula � can be satisﬁed in an irreﬂexive canonical-like model.
Let’s now think about the second kind of problem. Concretely, how can we prove
that we have not destroyed the nice properties of the canonical frame by moving
to a subframe? In particular, how can we ascertain density? We will see that here
�,
we will make good use of the special naming property of the formulas ����
namely that they can be used as identiﬁers of MCSs.

�

�

Lemma 4.74 Let � be a diamond saturated collection of witnessing maximal
consistent sets of formulas, and let � denote the relation �
� restricted to � . Then
the frame �

� is a non-branching, unbounded, dense, strict ordering.

�� �

238

4 Completeness

Proof. Let � and � be as in the statement of the lemma. Clearly, �
� is a
subframe of the canonical frame; hence, it inherits every universal property of �,
such as transitivity or non-branching. Irreﬂexivity follows from the fact that � �
for no witnessing � . This shows that � is a non-branching, strict ordering of � .

�� �

�

�

Unboundedness is not a universal condition, but nevertheless follows rather eas-
� are theorems of the logic
ily: simply use the fact that the formulas �
and hence, belong to every maximal consistent set. Unboundedness then follows
by the diamond saturation of � .

� and �

The case of density is more difﬁcult, and here’s where names are genuinely
useful. Assume that � and � are two MCSs such that � � �. We have to ﬁnd a
� in � that lies between � and �. Let � be the formula such that ����
MCS
�. It follows from � � � that �
ﬁnd that � �
with � � � and �

� . From this we may infer the existence of a MCS

� , so using the density axiom, we

�.

����

����

����

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

But is � � �? Note that since � is non-branching to the right, we already know
�,
�. Neither is it possible that � � �, for suppose
�, so by the transitivity

that � � � or �
since � �
otherwise. It would follows from � �
axiom, � �

� or � � �. But it clearly cannot be the case that �

�; but this would contradict the fact that �

�. �

� �

�

� that � � �

� and �

� �

�

�

�

�

�

�

�

We now have all the ingredients for the main theorem of this section:

Theorem 4.75 �

�

� is complete with respect to �

�

�

�.

� �

Proof. Given any consistent formula �, construct a countable, diamond saturated
set � of witnessing MCSs for �, as in the proof of Proposition 4.71. By the Truth
induced by � ;
Lemma 4.70, � is satisﬁable at some MCS
and by Lemma 4.74, this model is based on a non-branching, unbounded, dense,
strict ordering. But then the subframe generated by � is based on a countable,
dense, unbounded, strict total order and hence, isomorphic to the ordering of the
rationals. �

� in the model �

�

�

�

How widely applicable are these ideas? Roughly speaking, the situation is as fol-
lows. The basic idea is widely applicable; various rules for the undeﬁnable have
been employed in many different modal languages, and for many different classes
of models (we’ll see further examples in Chapter 7). Moreover, the use of such
rules can be fruitfully combined with other techniques, notably the step-by-step
method (this combination sometimes succeeds when all else fails). Rules for the
undeﬁnable are fast becoming a standard item in the modal logicians’ toolkit.

Nonetheless the method has its limitations, at least in the kinds of modal lan-
guages we have been considering so far. These limitations are centered on the
problem of working with submodels of the original canonical model.

4.7 Rules for the Undeﬁnable

239

As we saw, the ﬁrst problem — retaining sufﬁciently many MCSs for proving the
Truth Lemma — has a fairly satisfactory solution. Two remarks are in order here.

(i) The method only works well when we are working in tense logic. In the
proof of the ‘multiple Lindenbaum Lemma’, we crucially needed operators
for looking in both directions in order to show that it does not matter from
which perspective we describe a graph. If we have no access to the infor-
mation of nodes lying ‘behind’, we are forced to add a countably inﬁnite
family of more and more complex rules, instead of one single irreﬂexivity
rule.

But there are no problems in generalizing the proof of Lemma 4.71 to
similarity types with more than one tense diamond and/or versatile polyadic
operators. For example, in Exercise 4.7.3 is asked to use the method to
prove completeness for the language of PDL with converse programs.

(ii) Observe that we only proved weak completeness for �

�. This is be-
cause our proof of Lemma 4.71 only works with ﬁnite networks. In the
presence of names, however, it is possible to prove a stronger version of
� contains a name, other
Lemma 4.71; the basic idea is that when a MCS
MCSs may have complete access to the information in � through the ﬁnite
‘channel’ of � ’s name. For details we refer to Exercise 4.7.2.

�

�

There is a second problem which seems to be more serious. Which properties of
the canonical frame can we guarantee to hold on a trimmed down version? In
general, very little. Obviously, universal properties of the canonical model hold in
each of its submodels, and ﬁrst-order properties that are the standard translation of
� ���) are valid in each subframe for which a
closed modal formulas (such as �
Truth Lemma holds, but that is about it.

�

�

It is at this point where the names come in very handy. In fact, in order to prove
the inheritance of universal-existential properties like density, the names seem to
If, on the other hand, we have names at our disposal,
be really indispensable.
we can prove completeness results for a wide range of logics. Roughly speaking,
in case the logic is a tense logic, we can show that every Sahlqvist formula is
‘distinguishing-canonical’. The crucial observation is that the witnessing submodel
of the canonical model is a named model.

Deﬁnition 4.76 Let � be some modal similarity type. A � -model � is called
named if for every state � in � there is a formula � such that � is the only point in
� satisfying �. �

Theorem 4.77 Let � be some modal similarity type, and suppose that �
is a named � -model. Then for every very simple Sahlqvist formula �:

� �

�

�

� �

�

�

� iff �

�

��

(4.1)

240

4 Completeness

If, in addition, � is a versatile model for � , then (4.1) holds for every Sahlqvist
formula.

Proof. Let � be a named model. It was the aim of Exercise 1.4.7 to let the reader
show that the collection

�

�

�

�� �

�

� �

� a formula �

is closed under the boolean and modal operations. Hence, the structure �
is a general frame. Since � is named, � contains all singletons. The result then
follows from Theorem 5.90 in Chapter 5 — for the second part of the Theorem
Exercise 5.6.1 is needed as well. �

� �

� �

�

�

The use of rules for the undeﬁnable really comes into its own in some of the ex-
tended modal languages studied for Chapter 7. Two main paths have been explored,
and we will discuss both. In the ﬁrst, the difference operator is added to an ortho-
dox modal language. It is then easy to state a rule for the undeﬁnable (even if the
underlying modal language does not contain converse operators) and (by extending
the remarks just made) to prove a D-Sahlqvist theorem. In the second approach,
atomic formulas called nominals and operators called satisfaction operators are
added to an orthodox modal language. These additions make it straightforward to
deﬁne simple rules for the undeﬁnable (even if the underlying modal language does
not contain converse operators) and to prove a general completeness result without
making use of step-by-step arguments.

Exercises for Section 4.7
4.7.1 We are working in the basic modal similarity type. First, prove that a frame is intran-
� at every
sitive (�
state of the frame.
Second, let ��

� be the logic �, extended with the symmetry axiom �

�) iff we can falsify the formula �

� and the

� �

���

���

���

��

���

��

�

�

�

�

�

rule

(ITR)

if � �

�

��

�

�

�

�

� �

� then �

�, provided � does not occur in �,

Show that ��
frames.

� is sound and complete with respect to the class of symmetric, intransitive

4.7.2 Assume that we are working with the logic �
set � there is a diamond saturated set of MCSs � such that �

�. Show that for each consistent
� for some �

� .

�

�

�

�

(Hint: use a construction analogous to the one employed in the proof of Proposition 4.71.
Add an inﬁnite set of new variables to the language and ﬁrst prove that �
�� is
consistent for any new variable �. A network is now allowed to have one special node with
an inﬁnite label set, which should contain �
��. A description of a network is
now an inﬁnite set of formulas.)

����

����

� �

� �

�

�

�

�

4.7.3 Assume that we extend the language of PDL with a reverse program constructor:

� if � is a program then so is �

�

�.

4.8 Finitary Methods I

The intended accessibility relation of �
the axiom system of PDL (see Section 4.8), modulo the following changes:

� is the converse relation of �

�

�

. Let ���

241

be

�

(i) Add the converse axiom schemas �
(ii) Replace the Segerberg induction axiom with the following inﬁnitary rule:

� and �

�,

� �

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

(�–�)

If �

�

�

� �

�

�

� for all �

�, then �

�

�

�

�

� �

�

�.

Prove that this logic is sound and complete with respect to the standard models.

4.8 Finitary Methods I

In this section we introduce ﬁnite canonical models. We use such models to prove
weak completeness results for non-compact logics. We examine one of the best
known examples — propositional dynamic logic — in detail. More precisely, we
will axiomatize the validities regular (test free) propositional dynamic logic. Re-
call from Chapter 1 that this has a set of diamonds �
� indexed by a collection of
programs �. � consists of a collection of basic programs, and the programs gen-
erated from them using the constructors �, �, and �. A frame for this language is a
, but we are only interested in regular frames,
transition system �
that is, frames such that for all programs �, �

and �

:

�� �

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

We say that a formula � is a PDL-validity (written �
frames.

�) if it is valid on all regular

The collection of PDL-validities is not compact: consider the set

�

�

��

��

�

��

�

�

��

�

�

�

�� � � �

�

� ��

�

�

��

�

��

��

�

��

��

��

�

�

�

Any ﬁnite subset of � is satisﬁable on a regular frame at a single point, but �
itself is not. This compactness failure indicates that a strong completeness result
will be out of reach (recall Remark 4.44) so our goal (as with KL) should be to
prove a weak completeness result. It is is not too hard to come up with a candidate
axiomatization. For a start, the ﬁrst two regularity conditions given above can be
axiomatized by Sahlqvist axioms. The last condition is more difﬁcult, but even
here we have something plausible: recall that in Example 3.10 we saw that this last
condition is deﬁned by the formula set

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

� ��

� �

��

� �

�

�� � �

�

�

�

� �

� �

��

�

� �

�

�

�

�

�

�

This suggests the following axiomatization.

242

4 Completeness

Deﬁnition 4.78 A logic � in the language of propositional dynamic logic is a nor-
mal propositional dynamic logic if it contains every instance of the following ax-
iom schemas:

(i) �
(ii) �
(iii) �
(iv) �
(v) �
(vi) �

�

��

�

� � ��

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

� ��

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

��

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

� �

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

��

� �

�

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

�, for all
and is closed under modus ponens, generalization (�
programs �) and uniform substitution. We call the smallest normal propositional
� means that � is a theorem of PDL,
dynamic logic PDL.
consistency means PDL-consistency, and so on. �

In this section, �

� implies �

�

�

�

�

�

As we’ve already remarked, axioms (iii) and (iv) are (conjunctions of) Sahlqvist
axioms; they are canonical for the ﬁrst two regularity conditions, respectively. Fur-
ther, observe that Axiom (v) is a Sahlqvist formula as well; it is canonical for the
�. Thus we’ve isolated the difﬁcult part: axiom (vi),
condition �
which we will call the induction axiom for obvious reasons, is the formula we need
to think about if we are to understand how to cope with the canonicity failure. It is
probably a good idea for the reader to attempt Exercise 4.8.1 right away.

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

Proving the soundness of PDL is straightforward (though the reader should
(re-)check that the induction axiom really is valid on all regular frames). We will
prove completeness with the help of ﬁnite canonical models. Our work falls into
two parts. First we develop the needed background material: ﬁnitary versions of
MCSs, Lindenbaum’s Lemma, canonical models, and so on. Following this, we
turn to the completeness proof proper.

Recall that a set of formulas � is closed under subformulas if for all �

�

�, if

� is a subformula of � then �

�.

�

Deﬁnition 4.79 (Fischer-Ladner Closure) Let � be a set of formulas. Then � is
Fischer-Ladner closed if it is closed under subformulas and satisﬁes the following
additional constraints:

(i) If �
(ii) If �
(iii) If �

�

�

�

�

�

�

�

� then �

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

� then �

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

� then �

�

�

�

�

��

�

�

�.

�

If � is any set of formulas then FL�
smallest set of formulas containing � that is Fischer Ladner closed.

� (the Fischer Ladner closure of �) is the

�

4.8 Finitary Methods I

243

Given a formula �, we deﬁne �

� as the following formula:

if � is of the form �

� �

�

�

�

�

� otherwise�

�

�

A set of formulas � is closed under single negations if �

� belongs to � whenever

�.

�

�

We deﬁne �FL�

�

�, the closure of �, as the smallest set containing � which is

Fischer Ladner closed and closed under single negations. �

It is convenient to talk as if �
� really is the negation of �, and we often do so in
what follows. The motivation of closing a set under single negations is simply to
have a ‘connective’ that is just as good as negation, while keeping the set ﬁnite.
(If we naively closed under ordinary negation, then any set would have an inﬁnite
closure.)

It is crucial to note that if � is ﬁnite, then so is its closure. Some reﬂection on
the closure conditions will convince the reader that this is indeed the case, but it is
not entirely trivial to give a precise proof. We leave this little combinatorial puzzle
to the reader as Exercise 4.8.2.

We are now ready to deﬁne the generalization of the notion of a maximal con-

sistent set that we will use in this section.

Deﬁnition 4.80 (Atoms) Let � be a set of formulas. A set of formulas � is an
atom over � if it is a maximal consistent subset of �FL�
�. That is, � is an atom
over � if �
� then � is
� �FL�
inconsistent. ��

� is the set of all atoms over �. �

�, � is consistent, and if �

� �FL�

�

�

�

�

�

�

�

Lemma 4.81 Let � be any set of formulas, and � any element of ��

�

�. Then:

�

(i) For all �
(ii) For all �
(iii) For all �
(iv) For all �
(v) For all �

� �FL�

�

�: exactly one of � and �

� �FL�

�

�: �

�

�

�

�

�

� iff �

�

� is in �.
� or �

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

� �FL�
� �FL�

�: �
�: �

�

�

�

�

�

�

� iff �
� iff �

�

�

�

�

�

�

�

�.
� or �

�

�

�

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

�

�

�

�

�

�

�

�

�

� �FL�

�

�: �

�

�

�

�

�

� iff �

� or �

�

�

�

�

�

��

�

�

�.

�

Proof. With the possible exception of the last item, obvious. �

Atoms are a straightforward generalization of MCSs. Note, for example, that if we
choose � to be the set of all formulas, then ��
� is just the set of all MCSs. More
generally, the following holds:

�

�

Lemma 4.82 Let � be the set of all MCSs, and � any set of formulas. Then

��

�

�

�

� � �

� �FL�

�

�

�

� �

� ��

244

4 Completeness

Proof. Exercise 4.8.3. �

Unsurprisingly, an analog of Lindenbaum’s Lemma holds:

Lemma 4.83 If �
such that �

�.

�

� �FL�

�

� and � is consistent, then there is an �

�

�

�

��

�

Proof. If � is inﬁnite, the result is exactly Lindenbaum’s Lemma, so let us turn to
the more interesting ﬁnite case. There are two ways to prove this. We could simply
apply Lindenbaum’s Lemma: as � is consistent, there is an MCS
� that contains �.
Thus, by the previous lemma, �

� is an atom containing �.

� �FL�

�

But this is heavy handed: let’s look for a ﬁnitary proof instead. Note that the
�. We

information in an atom � can be represented by the single formula
will write such conjunctions of atoms as

�. Obviously

�.

�

�

�

�

�

��

Using this notation, we construct the desired atom as follows. Enumerate the
has been

�. Suppose that �

. Let �

be �

�

�

�

�

�

�

�

elements of �FL�
deﬁned, where � � �. We have that

� as �

� � � � � �

�

�

�

� �

�

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

��

��

as this is a propositional tautology, thus either �
consistent. Let �
atom containing �. �

� or �
be the consistent extension, and let � be �

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

� ��

� is
. Then � is an

��

�

�

Note the technique: we forced a ﬁnite sequence of choices between � and �
�.
Actually, we did much the same thing in the proof of Lemma 4.26, the Existence
Lemma for modal languages of arbitrary similarity type, and we’ll soon have other
occasions to use the idea.

Now that we have Lemma 4.83, it is time to deﬁne ﬁnite canonical models:

Deﬁnition 4.84 (Canonical Model over �) Let � be a ﬁnite set of formulas.
The canonical model over � is the triple �
� where for all
�, and for all atoms
propositional variables �, �

� � �

� �

��

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�� �

��

�

�

�

� and all programs �,

�

��

�

� if

�

�

� �

�

� is consistent �

� is called the canonical valuation, and the �

�

�

are called the canonical relations.

�

We generally drop the � superscripts. �

�

Although we have deﬁned it purely ﬁnitarily, the canonical model over � is ac-
tually something very familiar: a ﬁltration. Which ﬁltration? Exercise 4.8.4 asks
the reader to ﬁnd out. Further, note that although some of the above discussion is
speciﬁc to propositional dynamic logic (for example, the use of the Fischer Ladner

4.8 Finitary Methods I

245

closure) the basic ideas are applicable to any modal language. In Exercise 4.8.7 we
ask the reader to apply such techniques to the logic KL.

But of course, the big question is: does this ﬁnite canonical model work? Given
a consistent formula �, we need to satisfy � in a regular model. This gives two
natural requirements on the canonical model: ﬁrst, we need to prove some kind of
Truth Lemma, and second, we want the model to be regular. The good news is that
we can easily prove a Truth Lemma; the bad news is that we are unable to show
regularity. This means that we cannot use the canonical model itself; rather, we
for the atomic relations only, and deﬁne
will work with the canonical relations �
relations �

for the other programs in a way that forces the model to be regular.

�

�

Deﬁnition 4.85 (Regular PDL-model over �) Let � be a set of formulas. For
all basic programs �, deﬁne �
. For all complex programs, inductively
in the usual way using unions, compositions, and
deﬁne the PDL-relations �
reﬂexive transitive closures. Finally, deﬁne �, the regular PDL-model over �
� is the canonical valuation. Again, we
to be �
generally drop the � superscripts. �

�, where �

to be �

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

�

�

�

�

�

�

�

�

�

But of course, now the main question is, will be able to prove a Truth Lemma?
Fortunately, we can prove the key element of this lemma, namely, an Existence
Lemma (cf. Lemma 4.89 below). First the easy part. As the canonical relations �
are identical to the PDL-relations �

for all basic programs �, we have:

�

�

Lemma 4.86 (Existence Lemma for Basic Programs) Let � be an atom, and �
a basic program. Then for all formulas �
� iff there is a
�.

� such that ��

� in �FL�

� and �

�, �

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

� and �

Proof. This can be proved by appealing to the standard Existence Lemma and then
taking intersections (as in Lemma 4.83) — but it is more interesting to prove it
� such that
ﬁnitarily. For the right to left direction, suppose there is a �
�, thus
and �
� is consistent. As � is one of the conjuncts in
� is consistent.
� it must also be in �, for � is an atom and hence maximal
� is in �FL�
As �
�.
consistent in �FL�
For the left to right direction, suppose �

are identical for basic programs, ��

�. As �

�,

� �

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�. We construct an appropriate
.
is deﬁned such

� as �

� � � � � �

�

�

�

�

atom � by forcing choices. Enumerate the formulas in �FL�
Deﬁne �
that

�. Suppose as an inductive hypothesis that �

is consistent (where � �

� � �). We have

to be �

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

� �

�

� �

���

�

� � �

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

�

��

��

thus

�

�

�

� �

�

� ��

��

�

� � �

��

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

�

�

�

��

��

�

�

�

246

4 Completeness

Therefore either for �

�

�

� �

�

�

�

�

��

�

�

� is consistent. Choose �
. � is the atom we seek. �

�

� �

�

be �

�

�

��

� or for �

� we have that
to be this consistent expansion, and let �

� ��

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

and �

Now for the hard part. Axioms (v) and (vi) cannot enforce the desired identity
. But good news is at hand. These axioms are very strong and
between �
manage to ‘approximate’ the desired behavior fairly well. In particular, they are
for arbitrary programs �. This inclusion will
strong enough to ensure that �
enable us to squeeze out a proof of the desired Existence Lemma. The following
lemma is the crucial one.

�

�

�

�

Lemma 4.87 For all programs �, �

�

�

�.

�

� �

�

�

Proof. We need to show that for all programs �, if ��
� then there is a ﬁnite
�. Let
sequence of atoms �
� be the set of all atoms reachable from � by such a sequence. We will show that

such that �

� � � � � �

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

�

�

�

�

�

�

�

�

�

�

� �.
Deﬁne � to be

wise. Then �
would mean that

� �

�

�

�

�

�

��

� �

�. Note that �

� is inconsistent, for suppose other-
� would be consistent for at least one atom � not in �, which
� �. But then by
steps, which would imply

� was consistent for at least one �

� �

��

�

�

�

�

�

�, � could be reached from � in ﬁnitely many �

��

�

that �
As �

� � — which it is not.

�

�

�

� �

��

�

� is inconsistent, �

�

�

� �

�

�, hence by generalization � �

�

�

�

��

�

�. By axiom (vi), �

�

�

�

�

�

�

� �

�

�

�. Now, as ��

in �, thus �

�

�

� and hence �

�

�

� �

�

�

�

�

� �

�

�

� is consistent, it follows that

�

means that for one of the disjuncts
atoms, �

� and hence �

� �. �

�

�

�

�

�

� �

� of �,

�

�

�

�

�

�,

� is one of the disjuncts
�. As our initial assumption was that
� is consistent too. But this
� is consistent. As � and � are

��

�

�

�

�

�

�

�

With the help of this lemma, it is straightforward to prove the desired inclusion:

�

�

�

Lemma 4.88 For all programs �, �

�

.

�

�

�

Proof. Induction on the structure of �. The base case is immediate, for we deﬁned

to be �

�

�

�

for all basic programs �. So suppose ��

�, that is,
� is consistent as well. Using a ‘forcing

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

is consistent. By axiom (iii),
choices’ argument we can construct an atom � such that
are both consistent. But then, by the inductive hypothesis, ��
follows that ��

�. It
�, as required. A similar argument using axiom 4 shows that

� and
� and � �

�

�

�

�

�

� �

� �

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�.

�

�

�

�

�

�

The case for reﬂexive transitive closures follows from the previous lemma and

the observation that �

�

�

implies �

�

�

�

�

� �

�

�. �

�

�

�

�

We can now prove an Existence Lemma for arbitrary programs.

4.8 Finitary Methods I

247

Lemma 4.89 (Existence Lemma) Let � be an atom and let �
�FL�

� iff there is a � such that ��

�. Then �

� and �

�

�

�

�

�

�.

�

� be a formula in

�

�

�

�

Proof. The left to right direction puts the crucial inclusion to work. Suppose
� by ‘forcing choices’ in
� as

�. We can build an atom � such that ��

the now familiar manner. But we have just proved that �
well.

, thus ��

�

�

�

�

�

�

�

�

�

�

For the right to left direction we proceed by induction on the structure of �.
The base case is just the Existence Lemma for basic programs, so suppose � has
�. Thus there is
the form �
an atom � such that ��
�. By the Fischer Ladner
�, hence by the inductive hypothesis,
closure conditions, �
�. Hence by

� and � �
� belongs to �FL�

, and further suppose that ��

�. Similarly, as �

� is in �FL�

� and �

� and �

�, �

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

�

�

�

�

�

�

�

Lemma 4.81, �

�

�

�

�

�

�

�

�

�, as required.

We leave the case �

�

�

�

�

�

�

closure: suppose � is of the form �
means there is a ﬁnite sequence of atoms �

to the reader and turn to the reﬂexive transitive
�. This
, . . . ,
for all �; the

�. Assume that ��
, . . . , �

such that �

� and �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

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

required result for �

�. By a subinduction on � we prove that �
is then immediate.

�

�

Base case: �

� �. This means �

�

�

�. From axiom (v) we have that � �

�

�

�

�

�

�

�

�

� �

��

�

�

�, and hence that �

�

�

� �

�

�. Thus �

�

Inductive step. Suppose the result holds for �

�

�

�

�.
�, and that

�

�

�

�

�

�

�

�

, . . . , �

�

�

�

�.

�

�

�

�

�

�

��

By the inductive hypothesis, �
�FL�

�. But � �

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

. Hence �

�

�

��

�

�

�

�

�, for �

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

��

�

�. Hence �

�

�

�.

�

�

�

This completes the subinduction, and establishes the required result for �

�

�

�. It

also completes the main induction and thus the proof of the lemma. �

Lemma 4.90 (Truth Lemma) Let � be the regular PDL-model over �. For all
atoms � and all �

� �FL�

� iff �

�, �

�.

� �

�

�

�

Proof. Induction on the number of connectives. The base case follows from the
deﬁnition of the canonical valuation over �. The boolean case follows from
Lemma 4.81 on the properties of atoms. Finally, the Existence Lemma pushes
through the step for the modalities in the usual way. �

The weak completeness result for propositional dynamic logic follows.

Theorem 4.91 PDL is weakly complete with respect to the class of all regular
frames.

248

4 Completeness

Exercises for Section 4.8
4.8.1 Show that the induction axiom is not canonical.

4.8.2 Prove that for a ﬁnite set �, its closure set �FL�

�

� is ﬁnite as well.

4.8.3 Prove Lemma 4.82. That is, show that ��
� is the set of all MCSs, and � is any set of formulas.

�

�

� � �

� �FL�

�

�

�

� �

� ��, where

4.8.4 Show that the ﬁnite models deﬁned in the PDL completeness proofs are isomorphic
to certain ﬁltrations.

4.8.5 Show that for any collection of formulas �, � �

�

�

��

�

�

�

�.

�

4.8.6 Extend the completeness proof in the text to PDL with tests. Once you have found
an appropriate axiom governing tests, the main line of the argument follows that given in
the text. However because test builds modalities from formulas you will need to think
carefully about how to state and prove analogs of the key lemmas (such as Lemmas 4.87
and 4.88).

4.8.7 Use ﬁnite canonical models to show that KL is weakly complete with respect to the
class of ﬁnite strict partial orders (that is, the class of ﬁnite irreﬂexive transitive frames).
(Hint: given a formula �, let � be the set of all �’s subformulas closed under single nega-
tions. Let the points in the ﬁnite canonical model be all the maximal KL-consistent subsets
of �. For the relation �, deﬁne ���
� and (2) there
�, �
�. Use the natural valuation. You will need to make
is some �
�; bonus points if you can ﬁgure out how to prove this
use of the fact that �
yourself!)

� iff (1) for all �

� such that �

�� �

��

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

4.8.8 Building on the previous result, show that KL is weakly complete for the class of
ﬁnite transitive trees. (Hint: unravel.)

4.9 Finitary Methods II
As we remarked at the end of Section 4.4, although the incompleteness results show
that frame-theoretic tools are incapable of analyzing the entire lattice of normal
modal logics, they are capable of yielding a lot of information about some of its
subregions. The normal logics extending S4.3 are particularly well-behaved, and
in this section we prove three results about them. First, we prove Bull’s theorem:
all such logics have the ﬁnite frame property. Next, we show that they are all
ﬁnitely axiomatizable. Finally, we show that each of these logics has a negative
characterization in terms of ﬁnite sets of ﬁnite frames, which will be important
when we analyze their computational complexity in Chapter 6.

The logics extending S4.3 are logics of frames that are rooted, transitive, and
�)). To see this, recall that S4.3 has as axioms 4, T, and
connected (�
.3. These formulas are canonical for transitivity, reﬂexivity, and no branching to the
right, respectively. Hence any point-generated submodel of the canonical model

���

���

��

�

�

4.9 Finitary Methods II

249

generated

deﬁnable

�

�

�

�

�

submodel

�

variant

�

�

ﬁltration

bounded
morphism

�

�

�

�

�

�

�

elimination

Fig. 4.2. The models we will construct, and their relationships

for these logics inherits all three properties, and will in addition be rooted and
connected. Now, any connected model is reﬂexive. Thus rootedness, transitivity,
and connectedness are the fundamental properties, and we will call any frame that
has them an S4.3 frame. Note that any S4.3 frame can be viewed as a chain of
clusters (see Deﬁnition 2.43), a perspective which will frequently be useful in what
follows.

Bull’s Theorem

�, and for every formula � such that �

Our ﬁrst goal is to prove Bull’s theorem: all extensions of S4.3 have the ﬁnite
frame property. In Deﬁnition 3.23 we deﬁned the ﬁnite frame property as follows:
� has the ﬁnite frame property with respect to a class of ﬁnite frames F if and
only if � �
such that � is falsiﬁable on �. Using the terminology introduced in this chapter,
we can reformulate this more concisely as follows: � has the ﬁnite frame property
if and only if there is a class of ﬁnite frames � such that �
�. So, to prove
Bull’s Theorem, we need to show that if � extends S4.3, then any �-consistent
formula � is satisﬁable in a ﬁnite model �
In
short, Bull’s Theorem is essentially a general weak completeness result covering
all logics extending S4.3.

� there is some �

� such that �

�.

�� �� �

�� �

�

�

�

��

�

�

�

But how are we to build the required models? By transforming the canonical
model. Suppose � is �-consistent. Let � be any �-MCS containing �, and let
�,
� is based on an S4.3 frame. We are going to transform
� that satisﬁes � and is based on an S4.3 frame that

� generated by �. Then �

and (as just discussed) �

� into a ﬁnite model �

� be the submodel of �

� �

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

�

�

validates �.

Figure 4.2 shows what is involved. We are going to transform �

� in two distinct
ways. One involves taking a ﬁltration and eliminating certain points; this is the
technical heart of the proof. The other involves deﬁning a bounded morphism on
�; this part uses the results on deﬁnable variants and
a deﬁnable variant �

� of �

250

4 Completeness

distinguishing models proved in Section 3.4. These transformations offer us two
�, and together yield enough information to
perspectives on the properties of �
prove the result.

And so to work. We ﬁrst discuss the ﬁltration/elimination transformation. Let �

�, and let �

�

�

�

�

� �

�

�

� �

� �

be the (ﬁnite) set consisting of all subformulas of �
be the result of transitively ﬁltrating �
used in transitive ﬁltrations is deﬁned by �
all �
Filtration Theorem (Theorem 2.39) �
�. Moreover, �
all �
of the ﬁltration, thus �

� through �. Recall that the relation �
�, for
� . By the
�, and
� is a root
� is based on an S4.3 frame. Hence the frame underlying

� implies �
� iff �
�; see Lemma 2.42. As � is ﬁnite, so is �
�, for all �
� iff �

� is transitive, reﬂexive, and connected, and �

�, and all �� �

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

� is a ﬁnite chain of ﬁnite clusters.
Now for the key elimination step. We want to build a ﬁnite model based on a
frame for �. Now, we don’t know whether �
� is based on such a frame, but we
� to a ﬁnite distin-
do know that �
�. If we could transfer the truth of � in �
guishing model, then by item (iii) of Lemma 3.27 we would have immediately have
� is ﬁnite, and also (being a ﬁltration) dis-
Bull’s Theorem. Unfortunately, while �
�. This reﬂects something discussed
tinguishing, we have no guarantee that �
in Section 2.3: the natural map associated with a ﬁltration need not be bounded
morphism. It also brings us to the central idea of the proof: eliminate all points in
� which prevent the natural map from being a bounded morphism. Obviously,
� by eliminating points will be ﬁnite and distinguishing.
any model built from �
So the crucial questions facing us are: which points should be eliminated? And
how do we know that they can be thrown away without affecting the satisﬁability
of formulas in �?

�

�

�

Recall that the natural map associated with a ﬁltration sends each point � in
� in the ﬁltration. So if the natural
� is not a bounded
�� but

the original model to the equivalence class �
map from the frame underlying �
morphism, this means that for some � � �

� to the frame underlying �
� we have that �

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

or equivalently, that �

�

�� but

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

��

�

�

This motivates the following deﬁnition:

Deﬁnition 4.92 Suppose �, �
if there is a �

� such that for all �

�

� . We say that � is subordinate to � (� sub �)

�

�

�, it is not the case that �

�

��. �

�

So: if �
there is some �

� is not a bounded morphic image of �

� such that for some �

�

�

�

�

� under the natural map, then
�� and � sub �. We must

� , �

�

4.9 Finitary Methods II

251

get rid of all such �; we will call them eliminable points. But to show that we can
safely eliminate them, we need to understand the sub relation a little better.

Lemma 4.93
��.

�

�

(i) If � sub �, then there is a �

� such that for all �

�,

�

�

(ii) If � sub � then �
��.
(iii) The sub relation is transitive and asymmetric.
(iv) Suppose �, �, �

�

�

�

� such that � sub � and not � sub �. Then � sub � �

Proof. For item (i), note that by deﬁnition there is a �
it is not the case that �

� such that for all �
� is a connected relation, hence for every �

��. But �

�

�

�,
�,

�

�

�

�

element � of �, such that every element of � �
�. Hence (by the transitivity of �

��.
For item (ii), suppose � sub �. By item (i), this means that there is some
�, then
� too.
��. (It follows that if the natural map fails
This means that �
to be bounded morphism because of its behavior on the points � and �, then the
eliminable point � belongs to the same cluster as �.)

�-precedes �. Now if �
�) for all �

�, that is, �

�, �

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

Items (iii) and (iv) are left for the reader as Exercise 4.9.1. �

We are now ready for the key result: we can safely get rid of all the eliminable
points; there are enough non-eliminable points left to prove an Existence Lemma:

Lemma 4.94 (Existence Lemma) Let �
�, �
there is a �

� such that �

� �

�

�

��

�

�

�

�

�

�

� and suppose �
�, and �

�

� is not eliminable.

�

� �

�

�. Then

�

�

�

Proof. Construct a maximal sequence �
properties:

�

, �

, . . . through �

� with the following

�

(i) �
(ii) If � �

�

� �

�.

�

� and odd, then �

�

is some �

�

� such that �

�, �

�

�

�, and not

�

�

�

�

��

� sub �

�

�

.

�

��

(iii) If � �

� and even, then �

is some �

�

� such that �

�

�

�

�

�

and �

sub �

�

�.

�

�

�

��

��

�, and our goal is to ﬁnd a �

Here’s the basic idea. Think of this sequence as a series of moves through the
� -related �-containing point
model. We are given �
that is not eliminable. So, on our ﬁrst move (an odd move) we select an �
� -
related �-containing point (we are guaranteed to ﬁnd one, pretty much as in any
Existence Lemma). If the point is not-eliminable we have found what we need
and are ﬁnished. Unfortunately, the point may well be eliminable. If so, we make
a second move (an even move) to another point in the same cluster — namely a
point to which the ﬁrst point we found is subordinate. We iterate the process, and
eventually we will ﬁnd what we are looking for. We now make this (extremely
sketchy) outline precise.

252

4 Completeness

� in the sequence, �

�

�.

�

� �

�

�

� �, �

Claim 1. For every item �
If �
construction, hence �
also. Finally, if � �
construction, �

� �

�

�

�

�

�

�

�

�

� and by assumption �

�. If � �

� and odd, then �

� by

� �

�

�

�

�. As � is a �-MCS it contains �

�, thus �

�

�

�

�

�

� and even, then as we have just seen, �

hence �

� and hence �

�

�

�

�

� �

. By
�. This proves Claim 1.

��

�

�

�

�

�

��

Claim 2. The sequence terminates.
Suppose � is even. By property (iii), �
and by property (ii), it is not
. By
the case that �
item (ii) of Lemma 4.93, sub is a transitive and asymmetric relation, thus each �
,
for � even, is distinct. As there are only ﬁnitely many elements in �
� , the sequence
must terminate. This proves Claim 2.

sub �
. Hence by item 3 of Lemma 4.93, �

sub �

sub �

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

� such that �

�

�

�

�

�

�

�

��

��

Claim 3. The sequence does not terminate on even �.
Suppose � is even. We need to show that there is an �
and not �

� be �

sub �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

� � � � � �

�

�

�

�

�

�

such that not �

�

��

�

�

�

�� �

�

such that for all �, �

� sub �
�, for all �

. Let �
� there is a �

one of these points �
possible to choose such a � as �
By the Existence Lemma for normal logics (Lemma 4.20), there is a �
� and �
that �
contradiction that �
�. But �
We conclude that not �
choose �

, for some � �
��, hence (by transitivity) �
�, hence (recalling that �

��. Moreover, not �
� sub �
� and �

�. Then for each
. Let � be
�. (It is always
�.
� such
�. For suppose for the sake of a
�, and hence not
� — contradiction.
) we can always

�. This proves Claim 3.

� is connected.) As �

�, by Claim 1 �

�, for � �

�. Then �

� sub �

� sub �

to be �

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

�

�

�

�

�

�

�

�

�

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

We can now prove the result. By Claims 2 and 3, the sequence terminates on
�.
is not eliminable. By construction, for all even �,
. Hence by the

�, for some odd number �. By construction, �

. By item (ii) of Lemma 4.93, for all odd �, �

does not exist, �

�, hence �

Since �

� �

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

�

�

�

�

��

�

�

��

transitivity of �

� , �

�

�, and we are through. �

�

��

�

�

We now deﬁne the model �

� be the set of non-eliminable points in
� . (Note that by the previous lemma there must be at least one such point, for
� is a

� restricted to �

�. Hence �

�. Let �

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

�.) Then �
ﬁnite distinguishing model, and �

� �

�

�

�

� �

� is �
� is an S4.3 frame.

Lemma 4.95 �

� satisﬁes �.

Proof. First, we show by induction on the structure of � that for all �
all �
modalities. So suppose �
�, �
that �

�, and
�. The only interesting case concerns the
� such
�, hence by the

�. By the previous lemma, there is some �

� is not eliminable. As �

� iff �

�, and �

�, �

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

4.9 Finitary Methods II

253

�, hence �
inductive hypothesis, �
is straightforward; we leave it to the reader.

�

�

�

�

�

�

�

�

�

�

�

�

�

� as desired. The converse

It follows that � is satisﬁed somewhere in �

�. For, as �

�

�

�

Lemma 4.94 there is a non-eliminable �

�

� such that �

�

� and �

�

��

�

�

� �

�

�

�, by
�. Hence

�, and �

�

�

�

�

�

�

�

�

�. �

We are almost there. If we can show that �
guishing model, its frame validates � and we are through. Showing that �
will take us along the other path from �
will show that �

� is a ﬁnite distin-
�,
� shown in Figure 4.2. That is, we
�.

� to �
� is a bounded morphic image of a deﬁnable variant �

�, then as �

� of �

�

�

�

�

The required bounded morphism � is easy to describe: it agrees with the natural
map on all non-eliminable points, and where the natural map sent a point � to a
� will be a point ‘as close as possible’ to the
point that has been eliminated, �
�. Deﬁne
eliminated point. Let’s make this precise. Enumerate the elements of �

�

�

�

�

�

�

�

�

� by

� if �

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

� �

�

�

�

the ﬁrst element in the enumeration which is an �
element of �

�, otherwise.

�

�

�

�

�

�

�

�

�

�

�

�-minimal

� is ﬁnite, the minimality requirement (which captures the ‘as close as possi-

�

As �
ble’ idea) is well deﬁned.

�

�

�

�

� into �

As we will show, � is a bounded morphism from �

�.
But we have no guarantee that � is a bounded morphism from the model �
to �
�, for while the underlying frame morphism is ﬁne, we need to ensure that
the valuations agree on propositional symbols. We ﬁx this as follows. For any
��, and let �
propositional symbol �, deﬁne �
be �
� under
� is simply a variant of �
the mapping � . But it is not just any variant: as we will now see, it is a deﬁnable
variant. It is time to pull all the threads together and prove the main result.

� that agrees with �

�. That is, �

� to be �

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

�

Theorem 4.96 (Bull’s Theorem) Every normal modal logic extending ��
the ﬁnite frame property.

� has

�

� , then �

� is a deﬁnable variant of �

Proof. First we will show that �
equivalence classes that make up the ﬁltration �
can deﬁne any such �: the deﬁning formula �
� is simply a conjunction of all the
formulas in some subset of �, the set we ﬁltrated through. (Incidentally, we take
the conjunction of the empty set to be �.) It follows that �
for any propositional symbol �. To see this, note that �
or some ﬁnite collection of equivalence classes �
to be
deﬁne �

�. If � is any of the
�. Moreover, �

� can deﬁne �
� is either the empty set
�. In the former case,
deﬁnes
� is a deﬁnable

to be �. In the latter case, deﬁne �
� is �

. Either way, �

��. Thus �

�, for �

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

�

� � � � � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

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

254

4 Completeness

variant of �
constructed in the course of the proof.)

�. (Note that this argument makes use of facts about all four models

�

Next we claim that � is indeed a surjective bounded morphism from �
� onto
�; we show here that it satisﬁes the back condition and leave the rest to the
�, it is not eliminable, hence not
�-precedes an element

�. As �
�. But this means that every element in �

reader. Suppose �

� sub �

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

in �

�, as required.

�

�

�

and � is a �-consistent formula, build �

� satisﬁes �. Moreover �
right path through Figure 4.2. �
submodel of �

But now Bull’s Theorem follows. If � is a normal modal logic extending S4.3
� as described above. By Lemma 4.95,
�. To see this, simply follow the upper left-to-
�, for it is a generated
�, by Lemma 3.25 item (iii),
�, it too validates � as
� is a ﬁnite distinguishing model, hence, by Lemma 3.27 item (iii),

� is a bounded morphic image of �

� is a deﬁnable variant of �

�, hence so does �

�. Hence, as �

�. As �

�

�

�

�

�

�

�

required. But �
its frame validates � and we are through.

�

Finite axiomatizability

We now show that every normal logic extending S4.3 is ﬁnitely axiomatizable. (A
logic � is ﬁnitely axiomatizable if there is a ﬁnite set of formulas � such that �
is the logic generated by � .) The proof makes use of a special representation for
ﬁnite S4.3 frames.

Because every ﬁnite S4.3 frame is a ﬁnite chain of ﬁnite clusters, any such frame
can be represented as a list of positive integers: each positive integer in the list
records the cardinality of the corresponding cluster. For example, the list ��
represents the following frame:

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

�

�

�

��

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

���

�

�

�

��

�

�

�

���

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

Such representations will allow us to reduce the combinatorial heart of the follow-
ing proofs to a standard result about lists. The following deﬁnition pins down the
relationship between lists that will be important.

�

�

�

Deﬁnition 4.97 A list is a ﬁnite non-empty list of positive integers. A list t con-
tains a list s if t has a sublist of the same length as s, each item of which is greater

4.9 Finitary Methods II

255

or equal than the corresponding item of s. A list t covers a list s if t contains s and
the last item of t is greater than or equal to the last item of s. �

For example, the list ��
sublist, but it does not cover this list. But ��

��, for it has ��
��.
The modal relevance of list covering stems from the following lemma:

�� contains the list ��

��� covers ��

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

�

�� as a

Lemma 4.98 Let � and � be ﬁnite S4.3 frames, and let f and g be their associated
lists. Then f covers g iff there is a bounded morphism from � onto �.

Proof. Exercise 4.9.2. �

In view of this result, the following well-known result can be viewed as asserting
the existence of inﬁnite sequences of bounded morphisms:

Theorem 4.99 (Kruskal’s Theorem) Every countably inﬁnite sequence of lists �
in s, � � � implies
contains an inﬁnite subsequence � such that for all lists �

and �

�

�

covers �

.

�

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

a chain in � if for all �, �

Proof. Let us call a (ﬁnite or inﬁnite) subsequence �

of a sequence of lists
whenever � � �. We assume
�, �
familiarity with the notions of the head, the tail and the sum of a list. For instance,
�� and its sum is 19. Call � smaller than � if
�� is 8, its tail is ��
the head of ��
the sum of � is smaller than that of �.

covers �

�

�

�

�

�

�

�

�

�

�

�

�

�

In order to prove the lemma, we will show the following holds:

every countably inﬁnite sequence of lists � contains a chain of length 2.

(4.2)

Assume that (4.2) does not hold; that is, there are countably inﬁnite sequences
without chains of length 2 as subsequences.

Without loss of generality we may assume that � does not contain inﬁnitely many
of these one-
lists of length 1. For otherwise, consider its subsequence �
item lists. This subsequence may be identiﬁed with a sequence of natural numbers

�

�

�

�

�

�

. But

�

�

�

�

�

�

�

any sequence �

�

�

�

�

�

�

of natural numbers contains a subsequence

�

�

�

�

�

�

�

such that for all �� �

�, � � � implies �

�

�

�

�

�

�

(4.3)

. But then we
as can easily be proved. But if �
may also assume that � does not contain one-item lists at all: simply consider the
sequence found by eliminating all one-item lists.

then clearly �

covers �

�

�

�

�

�

�

Let � be a minimal such sequence. That is, � is a sequence of more-item lists,
, . . . such
, . . . has no

� has no 2-chains, and for all �, there are no more-item lists �
that �
2-chains.

, while the sequence �

is smaller than �

, �
, �

, . . . , �

, �

, �

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

256

4 Completeness

Now we arrive at the heart of the argument. Deﬁne �
sequences of the heads and the tails of �; that is, for each �, �

�

�

�

is the tail of �

�

�

�

. By (4.3), there is a subsequence �

�

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

as the
is the head of �
and
such that � � � implies

�

�

�

�

�

�

�

�

�

�

�

�

, whenever �� �

�. Now consider the corresponding subsequence �

�

�

�

�

�

�

�

of �. We need the following result:

any subsequence �

�

�

�

�

�

�

of tails of � contains a 2-chain�

(4.4)

By the same argument as before, we may assume that � contains only more-item
, and consider the
lists. Let � be the natural number such that �
and hence, smaller
sequence �
, . . . . Since �
that the mentioned sequence contains a
than �
2-chain. But obviously this 2-chain can only occur in the �-part of the sequence.
This proves (4.4).

is the tail of �
is the tail of �

, it follows by the minimality of �

, . . . , �

, �

, �

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

�

But if � contains a 2-chain, this means that there are two numbers � and � in
. But then

� with � � � and �

covers �

�

�

�

�

�

�

. Also, by deﬁnition of �, �
. This proves (4.2).

� �

�

�

� �

�

�

�

� �

� �

is covered by �

�

�

�

�

�

�

Finally, it remains to prove the lemma from (4.2). Let � be an arbitrary countably
inﬁnite sequence of lists. By successive applications of (4.2), it follows that �
contains inﬁnitely many chains. We claim that one these chains is inﬁnite. For if
we suppose that there are only ﬁnite chains, we may consider the sequence � of last
items of right-maximal ﬁnite chains in � (a chain is right-maximal if it can not be
extended to the right). There must be inﬁnitely many such right-maximal chains,
so � is an inﬁnite sequence. Hence, by yet another application of (4.2), � contains
a chain of length 2. But then some chain was not right-maximal after all. �

We now extract the consequences for logics extending S4.3:

Corollary 4.100 There is no inﬁnite sequence �
taining ��

� such that for all �, �

.

�

�

�

�

�

�

��

, �

, � � � of normal logics con-

�

Proof. Suppose otherwise. Then for some inﬁnite sequence of logics �
extending S4.3, and for all natural numbers �, there is a formula �

�

such that �

, �

, . . .

�

�

�

��

�

and �

�

�

�

�

�

�

��

. So, by Bull’s Theorem, for all natural numbers � there is a
. Let � be the inﬁnite
. By the Kruskal’s Theorem,
. Hence by
covers �

that validates �
associated with the frames �

ﬁnite S4.3 frame �
sequence of lists �
there exist natural numbers � and �, such that � � � and �
Lemma 4.98 there is a bounded morphism from �
and we have a contradiction. �

and does not satisfy �

. It follows that �

onto �

�

�

�

�

�

�

�

�

�

�

�

�

Theorem 4.101 Every normal modal logic extending ��
able.

� is ﬁnitely axiomatiz-

�

4.9 Finitary Methods II

257

�

�

�

�

Proof. To arrive at a contradiction, we will assume that there does exist an ex-
tension � of S4.3 that is not ﬁnitely axiomatizable. We will construct a inﬁnite
sequence �
� � � � of extensions of S4.3, thus contradicting Corollary 4.100.
As � is not ﬁnitely axiomatizable, it must be a proper extension of S4.3. Let
to be the logic generated by
�, and deﬁne �
be an arbitrary formula in �
�. The latter inclusion is strict because � is
�. Then ��
be the logic
�. Continuing in this fashion we ﬁnd the required inﬁnite

not ﬁnitely axiomatizable. Hence, there exists �
generated by �
sequence �

� � � � of extensions of S4.3. �

. Let �

� �

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

A negative characterization
We turn to the ﬁnal task: showing that every normal logic extending S4.3 has a
negative characterization in terms of ﬁnite sets of ﬁnite frames. Once again, the
proof makes use of the representation of S4.3 frames as lists of positive integers.

First some terminology. A set of lists � is ﬂat if for every two distinct lists in �,
neither covers the other. In view of Lemma 4.98, the modal relevance of ﬂatness
is this: if two frames are associated with distinct lists belonging to a ﬂat set, then
neither frame is a bounded morphic image of the other.

Lemma 4.102 All ﬂat sets are ﬁnite. Furthermore, for any set of lists � there is a
maximal set � such that �

� and � is ﬂat.

�

Proof. Easy consequences of Kruskal’s Theorem. �

If � is a ﬂat set of lists, then �
� is the set of lists covered by some list in �.
� is
�. If � is a set of lists, then �
Note that �
the class of all ﬁnite S4.3 frames � such that there is a bounded morphism from �
onto some frame whose list is in �.

� is ﬁnite and that �

�

�

�

�

�

�

�

�

�

�

Theorem 4.103 For every normal modal logic � extending S4.3 there is a ﬁnite set
� of ﬁnite S4.3 frames with the following property: for any ﬁnite frame �, �
iff � is an S4.3 frame and there does not exist a bounded morphism from � onto
any frame in �.

�

�

Proof. Let �
which do not validate �. Let � be a maximal ﬂat set such that �

� be the set of lists associated with ﬁnite S4.3 frames
�. Note that

� S4.3, and let �

�

�

�

�

�

�

� �

�.

We claim that for any ﬁnite S4.3 frame �, �

��. The left to
� validates �,
right implication is clear, for as no frame whose list belongs to �
there cannot be a bounded morphism from � onto any such frame. For the other
�. Let �’s list be f. Then
direction, we show the contrapositive. Suppose that �

� iff �

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
258

4 Completeness

�

�

�

�

�

�

�

� or f �

�. Now either f �

f �
morphism on � guarantees that �
f �
ﬂat subset of �
frame � whose list is g is a bounded morphic image of �, hence �
required. This completes the proof of the claim.

�, then the identity
�� as required. So suppose instead that
�), hence as � is a maximal
�, f must cover some list g in �. Thus by Lemma 4.98, any S4.3
�� as

�. This means that f ��

�. If f �

� (as �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

We can now deﬁne the desired ﬁnite set �: for each g �

�, choose a frame

�

�

�

whose list is g, and let � be the set of all our choices. �

Exercises for Section 4.9
4.9.1 Show that the sub relation is transitive and asymmetric. Furthermore, show that if
� sub � and not � sub �, then � sub � �

4.9.2 Prove Lemma 4.98. That is, let � and � be ﬁnite S4.3 frames, and let f and g be their
associated lists. Then show that f covers g iff there is a bounded morphism from � onto
�. (First hint: look at how we deﬁned the bounded morphism used in the proof of Bull’s
theorem. Second hint: look at the statement (but not the proof!) of Lemma 6.39.)

4.9.3 Give a complete characterization of all the normal logics extending S5. Your answer
should include axiomatizations for all such logics.

�

�

�

� be the smallest tense logic containing �, � , �

4.9.4 Let �
. Show that there
are tense logics extending �
� that do not have the ﬁnite frame property. (Hint: look
at the tense logic obtained by adding the Grzegorczyk axiom in the operator � . Is the
Grzegorczyk axiom in � satisﬁable in a model for this logic? Is the Grzegorczyk axiom in
� satisﬁable in a ﬁnite model for this logic?)

and �

�

�

�

�

�

�

�

4.10 Summary of Chapter 4
� Completeness: A logic � is weakly complete with respect to a class of structures
It is strongly complete with
S if every formula valid on S is a �-theorem.
respect to S if whenever a set of premises entails a conclusion over S, then the
conclusion is �-deducible from the premises.

� Canonical Models and Frames: Completeness theorems are essentially model
existence theorems. The most important model building technique is the canon-
ical model construction. The points of the underlying canonical frames are max-
imal consistent sets of formulas, and the relations and valuation are deﬁned in
terms of membership of formulas in such sets.

� Canonicity Many formulas are canonical for a property � . That is, they are
valid on any frame with property � , and moreover, when used as axioms, they
guarantee that the canonical frame has property � . When working with such
formulas, it is possible to prove strong completeness results relatively straight-
forwardly.

4.10 Summary of Chapter 4

259

� Sahlqvist’s Completeness Theorem: Sahlqvist formulas not only deﬁne ﬁrst-
order properties of frames, each Sahlqvist formula is also canonical for the ﬁrst-
order property it deﬁnes. As a consequence, strong completeness is automatic
for any logic that is axiomatized by axioms in Sahlqvist form.

� Limitative Results: The canonical model method is not universal:

there are
weakly complete logics whose axioms are not valid on any canonical frame. In-
deed, no method is universal, for there are logics that are not sound and weakly
complete with respect to any class of frames at all.

� Unraveling and Bulldozing: Often we need to build models with properties for
which no modal formula is canonical. Sometimes this can be done by transform-
ing the logic’s canonical model so that it has the relevant properties. Unraveling
and bulldozing are two useful transformation methods.

� Step-by-step: Instead of modifying canonical models directly, the step-by-step
method builds models by selecting MCSs. Because it builds these selections
inductively, it offers a great deal of control over the properties of the resulting
model.

� Rules for the Undeﬁnable: By enriching our deductive machinery with special
proof rules, it is sometimes possible to construct canonical models that have the
desired properties right from the start, thus avoiding the need to massage the
(standard) canonical model into some desired shape.

� Finitary Methods: The canonical model method establishes strong complete-
ness. Only weak completeness results are possible for for non-compact logics
such as propositional dynamic logic, and ﬁnite canonical models (essentially
ﬁltrations of standard canonical models) are a natural tool for proving such re-
sults.

� Logics extending S4.3: Although the incompleteness results show that a frame
based analysis of all normal logics is impossible, many subregions of the lattice
of normal modal logics are better behaved. For example, the logics extend-
ing S4.3 all have the ﬁnite frame property, are ﬁnitely axiomatizable, and have
negative characterizations in terms of ﬁnite frames.

Notes

Modal completeness results can be proved using a variety of methods. Kripke’s
original modal proof systems (see [290, 291] were tableaux systems, and com-
pleteness proofs for tableaux typically don’t make use of MCSs (Fitting [145] is
a good introduction to modal tableaux methods). Completeness via normal form
arguments have also proved useful. For example, Fine [139] uses normal forms to
prove the completeness of the normal logic generated by the McKinsey axiom; this
logic is not canonical (see Goldblatt [193]).

Nonetheless, most modal completeness theory revolves, directly or indirectly,

260

4 Completeness

around canonical models; pioneering papers include Makinson [314] (who uses a
method tantalizingly close to the step-by-step construction to pick out generated
subframes of canonical models) and Cresswell [97]. But the full power of canoni-
cal models and completeness-via-canonicity arguments did not emerge clearly till
the work of Lemon and Scott [303]. Their monograph stated and proved the Canon-
ical Model Theorem and used completeness-via-canonicity arguments to establish
many important frame completeness results. One of their theorems was a general
� �.
canonicity result for axioms of the form �
Although not as general as Sahlqvist’s [388] later result (Theorem 4.42), this cov-
ered most of the better known modal systems, and was impressive testimony to the
generality of the canonical model method.

�, where �, �, �, �

�

�

�

�

�

�

�

�

�

That KL is weakly complete with respect to the class of ﬁnite transitive trees
is proved in Segerberg [396]. (Strictly speaking, Segerberg proved that KL4 is
complete with respect to the transitive trees, as it wasn’t then known that 4 was
derivable in KL; derivations of 4 were independently found by De Jongh, Kripke,
and Sambin: see Boolos [67, page 11] and Hughes and Cresswell [241, page 150].)
Segerberg ﬁrst proves weak completeness with respect to the class of ﬁnite strict
partial order (the result we asked the reader to prove in Exercise 4.8.7), however
he does so by ﬁltrating the canonical model for KL, whereas we asked the reader
to use a ﬁnite canonical model argument. Of course, the two arguments are in-
timately related, but the ﬁnite canonical model argument (which we have taken
from taken from Hughes and Cresswell [241, Theorem 8.4] is rather more direct.
Segerberg then proves weak completeness with respect to ﬁnite trees by unraveling
the resulting model (just as we asked the reader to do in Exercise 4.8.8).

The incomplete tense logic K�ThoM discussed in the text was the ﬁrst known
frame incomplete logic, and it’s still one of the most elegant and natural exam-
ples. It can be found in Thomason [427], and the text follows Thomason’s original
incompleteness proof. Shortly afterward, both Fine [137] and Thomason [427]
exhibited (rather complex) examples of incomplete logics in the the basic modal
language. The (much simpler) incomplete logic KvB examined in Exercise 4.4.2
is due to van Benthem [38]; KvB is further examined in Cresswell [96]. In Exer-
cise 4.4.3 we listed three formulas which jointly deﬁne a ﬁrst-order class of frames,
but which when used as axioms give rise to an incomplete normal logic; this exam-
ple is due to van Benthem [36]. Both the original paper and the discussion in [42]
are worth looking at. The logic of the veiled recession frame was ﬁrst axiomatized
by Blok [63]. It was also Blok [64, 65] who showed that incompleteness is the rule
rather than the exception among modal logics.

Although ﬁltration and unraveling had been used earlier to prove complete-
ness results, the systematic use of transformation methods stems from the work
of Segerberg [396]. Segerberg reﬁned the ﬁltration method, developed the bulldoz-
ing technique, and used them (together with other transformation) to prove many

4.10 Summary of Chapter 4

261

important completeness results, including characterizations of the tense logics of

�, �

�

� �

�, �

�

�, �

� �

�

� �

� and their reﬂexive counterparts.

�

�

� �

We do not know who ﬁrst developed the modal step-by-step method. Certainly
the idea of building models inductively is a natural one, and has long been used in
both algebraic logic (see [237]) and set-theory (see [410]). One inﬂuential source
for the method is the work of Burgess: for example, in [76] he uses it to prove
completeness results in Since-Until logic (see also Xu [458] for some instructive
step-by-step proofs for this language). Moreover, in [77], his survey article on
tense logic, Burgess proves a number of completeness results for the basic modal
language using the method. A set of lecture notes by De Jongh and Veltman [255] is
the source of the popularity among Amsterdam logicians. Recent work on Arrow
Logic uses the method (and the related mosaic method) heavily, often combined
with the use of rules for the undeﬁnable (see, for example, [326]). Step-by-step
arguments are now widely used in a variety of guises.

Gabbay [158] is one of the earliest papers on rules for the undeﬁnable, and one of
the most inﬂuential (an interesting precursor is Burgess [75], in which these rules
are used in the setting of branching time logic). Gabbay and Hodkinson [164] is an
important paper which shows that such rules can take a particularly simple form in
the basic temporal language. For rules in modal languages equipped with the D-
operator, see de Rijke [104] and Venema [439]. For rules in modal languages with
nominals, see Passy and Tinchev [362], Gargov and Goranko [171], Blackburn and
Tzakova [61], and Blackburn [55].

The axiomatization of PDL given in the text is from Segerberg’s 1977 abstract,
(see [400]). But there was a gap in Segerberg’s completeness proof, and by the
time he had published a full corrected version (see [402]) very different proofs by
Parikh [357] and Kozen and Parikh [279], had appeared. It seems that several other
unpublished completeness proofs were also in circulation at this time: see Harel’s
survey of dynamic logic [215] for details. The proof in the text is based on lecture
notes by Van Benthem and Meyer Viol [48].

Bull’s Theorem was the ﬁrst general result about the ﬁne structure of the lattice
of normal modal logics. Bull’s original proof (in [72]) was algebraic; the model-
theoretic proof given in the text is due to Fine [136]. A discussion of the relation-
ship between the two proofs may be found in Bull and Segerberg [73]. Moreover,
Goldblatt [183] presents Fine’s proof from a rather different perspective, empha-
sizing a concept he calls ‘clusters within clusters’; the reader will ﬁnd it instructive
to compare Goldblatt’s presentation with the one in the text, which uses Fine’s
original argument. Fine’s paper also contains the ﬁnite axiomatizability result for
logics extending S4.3 (Theorem 4.101) and the (negative) characterization in terms
of ﬁnite sets of ﬁnite frames (Theorem 4.103), and the text follows Fine’s original
proofs here too.

The work of Bull and Fine initiated a (still ﬂourishing) investigation into subre-

262

4 Completeness

gions of the lattice of normal modal logics. For example, the position of logics in
the lattice characterized by a single structure is investigated in Maksimova [317],
Esakia and Meskhi [132] and (using algebraic methods) Blok [65]. In [138] and
[141], Fine adapts his methods to analyze the logics extending K4.3 (the adapta-
tion is technically demanding as not all these logics have the ﬁnite frame prop-
erty). Moreover, the Berlin school has a long tradition in this area: see Rauten-
berg [374, 375, 376], Kracht [283, 285, 286], and Wolter [452]. More recently,
the structure of the lattice of tense logics has received attention: see, for exam-
ple, Kracht [281] and Wolter [450]. And Wolter [451] investigates the transfer of
properties when the converse operator � is added to a logic (in the basic modal
language) that extends K4, obtaining various axiomatizability and decidability re-
sults.

Work by Zakharyaschev has brought new ideas to bear. As we pointed out in
the Notes to Chapter 3, in the 1960s (the early years following the introduction
of relational semantics for modal logic) it was hoped that one could describe and
understand any modal formula by imposing ﬁrst-order conditions on its frames.
But the incompleteness results, and the discovery of modal formulas that do not
correspond to any ﬁrst-order conditions, destroyed this hope. In a series of pa-
pers Zakharyaschev [462, 463, 464, 465] has studied an alternative, purely frame-
theoretic approach to the classiﬁcation of modal formulas. Given a modal (or intu-
itionistic) formula �, one can effectively construct ﬁnite rooted frames �
such that a general frame � refutes � iff there is a (not necessarily generated) sub-
� of � which satisﬁes certain natural conditions and which can be mapped
frame �
by a bounded morphism. Conversely, with every ﬁnite rooted
to one of the �
frame � Zakharyaschev associates a canonical formula which can be refuted on
a frame iff that frame contains a subframe (satisfying certain natural conditions)
that can be mapped to � by a bounded morphism. Like the search for ﬁrst-order
characterizations, the classiﬁcation approach in terms of canonical formulas is not
universal either. But its limitations are of a different kind: it only characterizes
transitive general frames — but for every modal (and intuitionistic) formula. Za-
kharyaschev [459] is a very accessible survey of canonical formulas, with plenty
of motivations, examples and deﬁnitions; technical details and discussions of the
algebraic and logical background of canonical formulas are provided by Chagrov
and Zakharyaschev [86, Chapter 9].

, . . . , �

�

�

�


