3

Frames

As we saw in Section 1.3, the concept of validity, which abstracts away from the
effects of particular valuations, allows modal languages to get to grips with frame
structure. As we will now see, this makes it possible for modal languages to deﬁne
classes of frames, and most of the chapter is devoted to exploring this idea.

The following picture will emerge. Viewed as tools for deﬁning frames, every
modal formula corresponds to a second-order formula. Although this second-order
formula sometimes has a ﬁrst-order equivalent, even quite simple modal formulas
can deﬁne classes of frames that no ﬁrst-order formula can. In spite of this, there
are extremely simple ﬁrst-order deﬁnable frame classes which no modal formula
can deﬁne. In short, viewed as frame description languages, modal languages ex-
hibit an unusual blend of ﬁrst- and second-order expressive powers.

The chapter has three main parts. The ﬁrst, consisting of the ﬁrst four sections,
introduces frame deﬁnability, explains why it is intrinsically second-order, presents
the four fundamental frame constructions and states the Goldblatt-Thomason The-
orem, and discusses ﬁnite frames. The second part, consisting of the next three
sections, is essentially a detailed exposition of the Sahlqvist Correspondence The-
orem, which identiﬁes a large class of modal formulas which correspond to ﬁrst-
order formulas. The ﬁnal part, consisting of the last section, studies further frame
constructions and gives a model-theoretic proof of the Goldblatt-Thomason theo-
rem. With the exception of the last two sections, all the material in this chapter lies
on the basic track.

Chapter guide

Section 3.1: Frame Deﬁnability (Basic track). This section introduces frame de-
ﬁnability, and gives several examples of modally deﬁnable frame classes.
Section 3.2: Frame Deﬁnability and Second-Order Logic (Basic Track). We ex-
plain why frame deﬁnability is intrinsically second-order, and give exam-

124

3.1 Frame Deﬁnability

125

ples of frame classes that are modally deﬁnable but not ﬁrst-order deﬁn-
able.

Section 3.3: Deﬁnable and Undeﬁnable Properties (Basic track). We ﬁrst show
that validity is preserved under the formation of disjoint unions, generated
subframes and bounded morphic images, and anti-preserved under ultraﬁl-
ter extensions. We then use these constructions to give examples of frame
classes that are not modally deﬁnable, and state the Goldblatt-Thomason
Theorem.

Section 3.4: Finite Frames (Basic track). Finite frames enjoy a number of pleas-
ant properties. We ﬁrst prove a simple analog of the Goldblatt-Thomason
Theorem for ﬁnite transitive frames. We then introduce the ﬁnite frame
property, and show that a normal modal logic has the ﬁnite frame property
if and only if it has the ﬁnite model property.

Section 3.5: Automatic First-Order Correspondence (Basic track). Here we pre-
pare for the proof of the Sahlqvist Correspondence Theorem in the follow-
ing section. We introduce positive and negative formulas, and show that
their monotonicity properties can help eliminate second-order quantiﬁers.
Section 3.6: Sahlqvist Formulas (Basic track). In this section we prove the Sahl-
qvist Correspondence Theorem. Our approach is incremental. We ﬁrst
explore the key ideas in the setting of two smaller fragments, and then
state and prove the main result.

Section 3.7: More About Sahlqvist Formulas (Advanced track). We ﬁrst discuss
the limitations of the Sahlqvist Correspondence Theorem. We then prove
Kracht’s Theorem, which provides a syntactic description of the ﬁrst-order
formulas that can be obtained as translations of Sahlqvist formulas.
Section 3.8: Advanced Frame Theory (Advanced track). We ﬁnish off the chap-
ter with some advanced material on frame constructions, and prove the
Goldblatt-Thomason Theorem model-theoretically.

3.1 Frame Deﬁnability

This chapter is mostly about using modal formulas to deﬁne classes of frames. In
this section we introduce the basic ideas (deﬁnability, and ﬁrst- and second-order
frame languages), and give a number of examples of modally deﬁnable frames
classes. Most of these examples — and indeed, most of the examples given in this
chapter — are important in their own right and will be used in later chapters.

Frame deﬁnability rests on the notion of a formula being valid on a frame, a
concept which was discussed in Section 1.3 (see in particular Deﬁnition 1.28). We
ﬁrst recall and extend this deﬁnition.

Deﬁnition 3.1 (Validity) Let � be a modal similarity type. A formula � (of this

126

3 Frames

similarity type) is valid at a state � in a frame � (notation: �
course, � is a frame of type � ) if � is true at � in every model �
is valid on a frame � (notation: �
� is valid on a class of frames � (notation: �
in �. We denote the class of frames where � is valid by ��

�; here, of
� � � based on �; �
�) if it is valid at every state in �. A formula
�) if it is valid on every frame �

.

� �

�

�

�

�

These concepts can be extended to sets of formulas in the obvious way. In par-
ticular, a set � of modal formulas (of type � ) is valid on a frame � (also of type
� ) if every formula in � is valid on �; and � is valid on a class � of frames if �
is valid on every member of �. We denote the class of frames where � is valid by

�

. �

��

�

Now for the concept underlying most of our work in this chapter:

Deﬁnition 3.2 (Deﬁnability) Let � be a modal similarity type, � a modal formula
of this type, and � a class of � -frames. We say that � deﬁnes (or characterizes) �
�. Similarly, if � is a set of modal
if for all frames �, � is in � if and only if �
formulas of this type, we say that � deﬁnes � if � is in � if and only if �

� .

�

�

A class of frames is (modally) deﬁnable if there is some set of modal formulas

that deﬁnes it. �

In short, a modal formula deﬁnes a class of frames if the formula pins down pre-
cisely the frames that are in that class via the concept of validity. The following
generalization of this concept is sometimes useful:

Deﬁnition 3.3 (Relative Deﬁnability) Let � be a modal similarity type, � a modal
formula of this type, and � a class of � -frames. We say that � deﬁnes (or charac-
terizes) a class � of frames within � (or relative to �) if for all frames � in � we
have that � is in � if and only if �

�.

�

Similarly, if � is a set of modal formulas of this type, we say that � deﬁnes a
class � of frames within � (or relative to �) if for all frames � in � we have that �
is in � if and only if �

� . �

�

Note that when � is the class of all � -frames, deﬁnability within � is our original
notion of deﬁnability. In Section 3.4 we will investigate which frames are deﬁnable
within the class of ﬁnite transitive frames, but for the most part we will work with
the ‘absolute’ notion of deﬁnability given in Deﬁnition 3.2.

We often say that a formula � (or a set of formulas � ) deﬁnes a property (for
example, reﬂexivity) if it deﬁnes the class of frames satisfying that property. For
� deﬁnes the class of reﬂexive frames; in
example, we will shortly see that � �
practice, we would often simply say that � �

� deﬁnes reﬂexivity.

�

�

Up till now our discussion has been purely modal — but of course, as frames are
just relational structures, we are free to deﬁne frame classes using a wide variety of

3.1 Frame Deﬁnability

127

non-modal languages. For example, the class of reﬂexive frames is simply the class
of all frames that make �� ��� true. In this chapter, we are interested in comparing
modal languages with the following classical languages as tools for deﬁning frame
classes:

Deﬁnition 3.4 (Frame Languages) For any modal similarity type � , the ﬁrst-
order frame language of � is the ﬁrst-order language that has the identity symbol �
� for each �-ary modal operator � in
together with an � � �-ary relation symbol �
. We often call it the ﬁrst-order correspondence
� . We denote this language by �
language (for � ).

�

�

�

�

�

Let � be any set of proposition letters. The monadic second-order frame lan-
guage of � over � is the monadic second-order language obtained by augmenting
with a �-indexed collection of monadic predicate variables. (That is, this lan-
, and in addition is capable of quantifying over
guage has all the resources of �
���, though sometimes we sup-
subsets of frames.) We denote this language by �
. Moreover, we often simply call it the second-
press reference to � and write �
order frame language or the second-order correspondence language (for � ), taking
it for granted that only monadic second-order quantiﬁcation is permitted. �

�

�

�

�

�

�

Note that the second-order frame language is extremely powerful, even for the
basic modal similarity type. For example, if � is interpreted as the relation of set
membership, second-order ZF set theory can be axiomatized by a single sentence
of this language.

Deﬁnition 3.5 (Frame Correspondence) If a class of frames (or more informally,
a property) can be deﬁned by a modal formula � and by a formula � from one of
these frame languages, then we say that � and � are each others (frame) correspon-
dents. �

For example, the basic modal formula � �
� and the ﬁrst-order sentence �����
� deﬁnes reﬂexivity. Later
are correspondents, for we will shortly see that � �
in this chapter we will show how to systematically ﬁnd correspondents of modal
formulas by adopting a slightly different perspective on the standard translation
introduced in Section 2.4.

�

�

In Deﬁnition 3.5 we did mention the possibility that modal formulas correspond
to a set of ﬁrst-order formulas. Why not? The reason is that this situation simply
cannot occur, as we ask the reader to show in Exercise 3.8.3.

There are a number of practical reasons for being interested in frame deﬁnabil-
ity. First, some applications of modal logic are essentially syntactically driven;
their starting point is some collection of modal formulas expressing axioms, laws,
or principles which for some reason we ﬁnd interesting or signiﬁcant. Frame de-
ﬁnability can be an invaluable tool in such work, for by determining which frame

128

3 Frames

classes these formulas deﬁne we obtain a mathematical perspective on their con-
tent. On the other hand, some applications of modal logic are essentially seman-
tically driven; their starting point is some class of frames of interest. But here too
deﬁnability is a useful concept. For a start, can the modal language distinguish the
‘good’ frames from the ‘bad’ ones? And which properties can the modal language
express within the class of ‘good’ frames? Finally, many applied modal languages
contain several modalities, whose intended meanings are interrelated. Sometimes
it is clear that these relationships should validate certain formulas, and we want to
extract the frame-theoretic property they correspond to. On the other hand it may
be clear what the relevant frame-theoretic property is (for example, in the basic
temporal language we want the � and � operators to scan backwards and forward
along the same relation) and we want to see whether there is a modal formula that
deﬁnes this property. In short, thinking in terms of frame deﬁnability can be useful
for a variety of reasons — and as the following examples will make clear, modal
languages can deﬁne some very interesting frame classes indeed.

Example 3.6 In Example 1.10 in Section 1.2 we mentioned the following reading
� as ‘necessarily
of the modalities: read �
�’. We also mentioned that a number of interesting looking principles concerning
necessity and possibility could be stated in the basic modal language. Here are
three important examples, together with their traditional names:

� as ‘it is possibly the case that �’ and �

(T) � �
(4) ��
(5) �

�

�

� �

�

�

� �

��

�

But now the problems start. While the status of T seems secure (if � holds here-
and-now, � must be possible) but what about 4 and 5? When we have to deal with
embedded modalities, our intuitions tend to fade, even for such simple formulas as
4 and 5; it is not easy to say whether they should be accepted, and if we only have
our everyday understanding of the words ‘necessarily’ and ‘possibly’ to guide us, it
is difﬁcult to determine whether these principles are interrelated. What we need is
a mathematical perspective on their content, and that is what the frame deﬁnability
offers. So let’s see what frame conditions these principles deﬁne.

Our ﬁrst claim is that for any frame �

� ��� ��, the axiom T corresponds to

reﬂexivity of the relation �:

� T iff �

�

�� �� ����

(3.1)

The proof of the right to left direction of (3.1) is easy: let � be a reﬂexive frame,
and take an arbitrary valuation � on �, and a state � in � such that �
�.
� holds at some state that is accessible from � — but as �
We need to show that �
is reﬂexive, � is accessible from itself, and �

�.

� � �� �

�

�

�

�

3.1 Frame Deﬁnability

129

For the other direction, we use contraposition: suppose that � is not reﬂexive,
that is, there exists a state � which is not accessible from itself. To falsify T in
�, it sufﬁces to ﬁnd a valuation � and a state � such that � holds at �, but �
does not. It is pretty obvious that we should choose � to be our irreﬂexive state
�. Now the valuation � has to satisfy two conditions: (1) � � � ��� and (2)
�. Consider the minimal valuation � satisfying

�� � � � ���� � � ��� �

�

condition (1), that is, take

� ��� � ����

Then it is immediate that �
��� does not hold in �, � must be distinct from �, so � �

�. Now let � be an �-successor of �. As
�. As � was arbitrary,

� � �� �

�

�

�

�. This proves (3.1).

�

�

� �

Likewise, one can prove that for any frame �

� ��� ��

�

�

� iff � is transitive, and

�

�

� iff � is euclidean �

(3.2)

(3.3)

where a relation is euclidean if it satisﬁes ���� ����� � ��� � � ��� �. We leave
the proofs of (3.2) and the easy (right to left) direction of (3.3) to the reader. For
the left to right direction of (3.3), we again argue by contraposition. Assume that
� is a non-euclidean frame; then there must be states �, � and � such that ���,
���, but not ���:

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

� � �� �

� and �

We will try to falsify � in �; for this purpose we have to ﬁnd a valuation � such
�. In other words, we have to make � true
that �
at some �-successor � of �, and false at all �-successors of some �-successor �
of �. Some reﬂection shows that appropriate candidates for � and � are � and �,
respectively. Note that again the constraints on � are twofold: (1) � � � ��� and
(2) �� � ���� � � ��� �

�.

� � �� � �

��

�

�

Let us take a maximal � satisfying condition (2), that is, deﬁne

� ��� � �� � � � it is not the case that �����

�

�

�, so � �

�, since �
Now clearly � �
is in the set �� � � �
�. In other words,
it is not the case that ����. So �
we have indeed found a valuation � and a state � such that � does not hold in �.
Therefore, � is not valid in �. This proves (3.3). �

�. On the other hand we have �

��

�

�

�

�

130

3 Frames

Example 3.7 Suppose that we are working with the basic temporal language (see
Section 1.3 and in particular Example 1.25) and that we are interested in dense
bidirectional frames (that is, structures in which between every two points there is a
third). This property can be deﬁned using a ﬁrst-order sentence (namely ��� �� �
� � �� �� � � � � � ��) but can the basic temporal language deﬁne it too?

It can. The following simple formula sufﬁces: � � � � � �. To see this, let
� � � � � �. Suppose that a point � � � has
� �� � �� be a frame such that �
� satisfy the density condition, consider the

�. To show that � and �

�

�

a �-successor �
following minimal valuation �

guaranteeing that �

�

� �

�� �

�

� �:

�

�

�

��� � ��

��

�

�

Now, under this valuation �

�

� �, and by assumption �

� � �. This means there is a point � such that � � � and �

�

�

�

� � � � � �, hence
� is
� �. But as �
�, so � is the intermediate point

�

the only state where � holds, this implies that � � �
we were looking for.
Conversely, let �

valuation � , � � holds at some � � � . Then there is a point �
�. But as � is dense, there is a point � such that � � � � �

� �� � �� be a dense frame, and assume that under some
� and
� � and

� such that � � �
�, hence �

�

�

�

�

hence �

�

� � �.

Note that nothing in the previous argument depended on the fact that we were
working with the basic temporal language; the previous argument also shows that
�.
density is deﬁnable in the basic modal language using the formula �
Note that this is the converse of the 4 axiom that deﬁnes transitivity. �

� �

��

Example 3.8 Here’s a more abstract example. Suppose we are working with a
, and that we are in-
similarity type with three binary operators �
terested in the class of frames in which the three ternary accessibility relations
, respectively), offer, so to speak, three ‘perspectives’
(denoted by �
on the same relation. To put this precisely, suppose we want the condition

and �

and �

, �

, �

�

�

�

�

�

�

��� iff �

��� iff �

�

�

�

�

���

to hold for all �, � and � in such frame. Can we deﬁne this class of frames?
� we have

We can. We will show that for all frames �

� ��� �

� �

� �

�

�

�

�

�

� � ��

�� � �� � �

��

� iff �

�� ���� ��

��� � �

�����

(3.4)

�

�

�

�

�

�

�

�

(Recall that we use inﬁx notation for dyadic operation symbols.) The easy direction
����. Con-
is from right to left. Let � be a frame satisfying ���� ��
sider an arbitrary valuation � on � and an arbitrary state � such that �
���, �
�, so by �

� and there are states � and � with �

� and
��� we

���. But then �

��. Then, �

�. From �

��� � �

� � ��

� � �� �

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

have �

�

�� � �

�

��� we derive �
�.

��

�

�

�

3.2 Frame Deﬁnability and Second-Order Logic

131

�

�

�

��

�

�

For the other direction, suppose that the modal formula � � ��
� is valid in �, and consider states �, � and � in � with �

show that �
� ��� � ���. Then �
Hence, there must be states �
� it follows that � � �

���. We will
���. Consider a valuation � with � ��� � ���, � ��� � ��� and
�.
�. From
� and �
�, �
�. Again, using the truth deﬁnition
�. The latter two facts imply

� with �
�, so we have �

�, so by our assumption, �

� and �

��, �

��, �

�, �

�� � �� �

�

� � �� �

� � �

����

���

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

we ﬁnd states �
that �

� � and �

��

��

�� with �
� �. But then we have �

�

���, as required. �

From these examples the reader could easily get the impression that modal for-
mulas always correspond to frame properties that are deﬁnable in ﬁrst-order logic.
This impression is wrong, and in the next section we will see why.

�

Exercises for Section 3.1
3.1.1 Consider a language with two diamonds ��� and ���. Show that �
on precisely those frames for the language that satisfy the condition �
What sort of frames does �

� deﬁne?

� ������

��

� ������

�

�

�

��

�

� is valid
�.

��

�

�

3.1.2 Consider a language with three diamonds ���, ���, and ���. Show that the modal
� is valid on a frame for this language if and only if the frame
formula ���
satisﬁes the condition �
��.

� ������

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

3.2 Frame Deﬁnability and Second-Order Logic

In this section we show that modal languages can get to grips with notions that
exceed the expressive power of ﬁrst-order logic, and explain why. We start by pre-
senting three well-known examples of modal formulas that deﬁne frame properties
which cannot be expressed in ﬁrst-order logic. Then, drawing on our discussion of
the standard translation in Section 2.4, we show that such results are to be expected:
as we will see, modal formulas standardly correspond to second-order frame con-
ditions. Indeed, the real mystery is not why they do so (this turns out to be rather
obvious), but why they sometimes correspond to simple ﬁrst-order conditions such
as reﬂexivity or transitivity (we discuss this more difﬁcult issue in Sections 3.5–
3.7).

�

�

� � �� �

�, which we will call
Example 3.9 Consider the L¨ob formula �
� for brevity. This formula plays an essential role in provability logic, a branch of
� is read as ‘it is provable (in some formal system) that �’.
modal logic where �
The formula � is named after L¨ob, who proved � as a theorem of the provability
logic of Peano Arithmetic. We’ll ﬁrst show that � deﬁnes the class of frames
(A relation
��� �� such that � is transitive and �’s converse is well-founded.
� is well-founded if there is no inﬁnite sequence � � ���
; hence, �’s

��

��

�

�

�

�

132

3 Frames

converse is well-founded if there is no inﬁnite �-path emanating from any state. In
particular, this excludes cycles and loops.)

We’ll then show that this is a class of frames that ﬁrst-order frame languages

cannot deﬁne; that is, we’ll show that this class is not elementary.

To see that � deﬁnes the stated property, assume that �

� ��� �� is a frame
with a transitive and conversely well-founded relation �, and then suppose for the
sake of a contradiction that � is not valid in �. This means that there is a valuation
� and a state � such that �

�. In other words, �

� � �� �

� � �� � �

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

as �
that �

must have a successor �

�. Then � must have a successor �

� � ��, but � �
� � � holds at all successors of �, we have that �

such that �
�, and
�. This in turn implies
where � is false; note that by the transitivity of �,
is also a successor of �. But now, simply by repeating our argument, we see that
(which by transitivity must be a successor
must have a �-falsifying successor �
(which by transitivity must be a successor of
� � � �,
,
, �

In short, we have found an inﬁnite path ���

contradicting the converse well-foundedness of �. (Note that the points �
. . . need not all be distinct.)

), that �
), and so on.

has a successor �

of �

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

For the other direction, we use contraposition. That is, we assume that either �
is not transitive or its converse is not well-founded; in both cases we have to ﬁnd
a valuation � and a state � such that �
�. We leave the case where
� is not transitive to the reader (hint: instead of �, consider the frame equivalent
��) and only consider the second case. So assume that �
formula �
is transitive, but not conversely well-founded. In other words, suppose we have a
� � � �. We exploit the
transitive frame containing an inﬁnite sequence �
presence of this sequence by deﬁning the following valuation � :

� � �� � �

�� � �

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

� ��� � � � �� � � � there is an inﬁnite path starting from ���

�

� � � is true every-
� � ��. The claim then

We leave it to the reader to verify that under this valuation, �
where in the model, whence certainly, �
follows from the fact that �

�.
Finally, to show that the class of frames deﬁned by � is not elementary, an easy
compactness argument sufﬁces. Suppose for the sake of a contradiction that there
is a ﬁrst-order formula equivalent to �; call this formula �. As � is equivalent to �,
any model making � true must be transitive. Let �
� be the ﬁrst-order
formula stating that there is an �-path of length � through �

:

� � �� �

� � �� �

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

��

� � � � � �

� �

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

���

�

�
�
�
3.2 Frame Deﬁnability and Second-Order Logic

133

Obviously, every ﬁnite subset of

� � ��� � ����� ����� � ��� � � ��� �� � ��

� � � ��

�

is satisﬁable in a ﬁnite linear order, and hence in the class of transitive, conversely
well-founded frames. Thus by the Compactness Theorem, � itself must have a
model. But it is clear that � is not satisﬁable in any conversely well-founded
frame — and �, being equivalent to �, is supposed to deﬁne the class of transi-
tive, conversely well-founded frames. From this contradiction we conclude that �
cannot be equivalent to any ﬁrst-order formula.

Could � then perhaps be equivalent to an (inﬁnite) set of ﬁrst-order formulas?
No — we already mentioned (right after Deﬁnition 3.5 that this kind of correspon-
dence never occurs. �

Our next example concerns propositional dynamic logic (PDL). Recall that this
language contains a family of diamonds ���� � � � � � (where � is a collection of
programs) and the program constructors �, � and �. In the intended frames for this
language (that is, the regular frames; see Example 1.26) we want the accessibility
relations for diamonds built using these constructors to reﬂect choice, composition,
and iteration of programs, respectively. Now, to reﬂect iteration we demanded that
� used for the program �
� be the reﬂexive, transitive closure of
the relation �
used for �. But it is well-known that this constraint cannot be
the relation �
expressed in ﬁrst-order logic (as with the L¨ob example, this can be shown using
a compactness argument, and the reader was asked to do this in Exercise 2.4.5).
Because of this, when we discussed PDL at the level of models in Section 2.4 we
used the inﬁnitary language �
as the correspondence language for PDL; using
inﬁnite disjunctions enabled us to capture the ‘keep looking!’ force of � that eludes
ﬁrst-order logic. But although ﬁrst-order logic cannot get to grips with �, PDL itself
can — via the concept of frame deﬁnability.

�

�

�

�

�

Example 3.10 PDL can be interpreted on any transition system of the form �

�

�

�

�

�

�

��� �

. Let us call such a frame �-proper if the transition relation �

� of
� is the reﬂexive and transitive closure of the transition relation �
each program �
of �. Can we single out, by modal means, the �-proper frames within the class of
? And can we then go on to single
all transition systems of the form ��� �
out the class of all regular frames?

�

�

�

�

�

�

�

The answer to both questions is yes. Consider the following set of formulas

� � ���

��� � �� ��� � �� � ��

���� ��

�� � �� � �����

��� � � � � ��

�

�

�

�

As we mentioned in Example 1.15, ��
Segerberg’s axiom, or the induction axiom. We claim that for any PDL-frame �:

��� is called

��� � �� ��� � �� � ��

�

�

�

�

� iff � is �-proper �

(3.5)

134

3 Frames

The reader is asked to supply a proof of this in Exercise 3.2.1.

A straightforward consequence is that PDL is strong enough to deﬁne the class
of regular frames. The constraints on the relations interpreting � and � are simple
ﬁrst-order conditions, and

� � ���

� �

�� � ��

���

��� ��

� �

�� � ��

�� � ��

�� � � � � ��

�

�

�

�

�

�

�

�

pins down down what is required. So � � � deﬁnes the regular frames. �

In the previous two examples we encountered modal formulas that expressed frame
properties that were, although not elementary, still relatively easy to understand.
(Note however that in order to formally express (converse) well-foundedness in
a classical language, one needs heavy machinery — the inﬁnitary language �
does not sufﬁce!) The next example shows that extremely simple modal formulas
can deﬁne second-order frame conditions that are not easy to understand at all.

�

�

�

� does not
Example 3.11 We will show that the McKinsey formula ��
correspond to a ﬁrst-order condition by showing that it violates the L¨owenheim-
Skolem theorem.

� �

��

Consider the frame �

� ��� ��, where

� � ��� � ��

� �

� � �

� � � ��� ��� � ��

� � �

� ��� ����

�

�

�

���

�

�

�

and

� � ���� �

�� ��

� �

�� ��

� �

� � � �

� � � ��� ��� �

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

���

�

���� �

�� ��

� �

� � � �

� � �

� ��� ����

�

�

�

�

��

���

�

�

�

In a picture:

�

�

�

�

��

�

�

�

�

��

��

�

��

�

��

�

�

�

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

Note that � contains uncountably many points, for the set of functions indexing
the � points is uncountable.

Our ﬁrst observation is that �

�

��

��

� �

verify that for all � different from �, �

� �

�

��

�. We leave it to the reader to
�. As to showing that

��

� �

3.2 Frame Deﬁnability and Second-Order Logic

135

�

� �

�

��

� �

� � �� �

�

�

� � �� �

�

�

�

Choose � �
clearly, �

�

�

��

�, suppose that �
�. From this we get either �
� ��� �� such that �

�

�

�

��

�. Then, for each � �

�

� � �� �

�

��

��

� or �

�

�

� � �� �

�, for each � �

�

�,
�.
�. Then

�

��

��

�

�

�

�, and so �

�

� � �� �

�

�

�

��

���

�

�.

��

� � �� �

� � �� �

�

��

� �

In order to show that ��

� does not deﬁne a ﬁrst-order frame condition,
let’s view the frame � as a ﬁrst-order model with domain � . By the downward
L¨owenheim-Skolem Theorem (here we need the strong version of Theorem A.11)
there must be a countable elementary submodel �
� contains
� countable, there
�, and each �
�. Now,
must be a mapping � �
if the McKinsey formula was equivalent to a ﬁrst-order formula it would be valid
� are elementarily
on �
equivalent). But we will show that the McKinsey formula is not valid on �
�, hence
it cannot be equivalent to a ﬁrst-order formula.

� (the L¨owenheim-Skolem Theorem tells us that � and �

. As � is uncountable and �

� of � whose domain �

does not belong to �

� ��� �� such that �

and �

, �

��

��

��

��

�

�

�

�

�

Let �

� be a valuation on �

� such that �

�

��� � ��

� � �

�

�

��

���

�

�

does not belong to �

�. We will show that under �

�; here � is a
� is
�, ��

mapping such that �
true at �, but ��

�

� is not.

It is easy to see that �

�

�

�

� �

�� � �

�

��

�

�

��

��

��

��

, �

and �

� is false at each �

of �
in �
���� �� � ���. Observe that � is thus true at �
at �

; this means that �

�

�

��

���

�

�

�

�. For a start, since � holds at exactly one
. Now consider an arbitrary element �
� such that
, and, more interestingly, false

�

�

�

��

���

�

�. Then � is distinct from � , so there must be an element � �

has a successor where � is false, so �

�

�

�

� �

�� �

�

�

�. Hence, we have not been able to ﬁnd a successor for � where �

� holds, so

�

�

�

�

�

� �

�� � �

�

��

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

� �

� �

�� �

�� �

��

and �

�, for each state �

In order to show that �

� we reason as follows. Note ﬁrst that
�.
. Now consider an arbitrary element �
of � complementary if for all �, ���� � � � ����; the
Call two states �
reader should verify that this relation can be expressed in ﬁrst-order logic. Now
; since complementary states are unique,
suppose that �
� as
the fact that �
. Hence,
well. Clearly then, we may conclude that �
�. But
there exists some � �
then �

� is an elementary submodel of � would imply that �

� such that ���� � � ���. Therefore, �

� holds at every successor of �. �

is not complementary to �

is complementary to �

exists in �

of �

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

Clearly then, modal languages can express many highly complex properties via the
notion of frame validity. In fact, as was shown by S.K. Thomason for the basic
modal similarity type, the consequence relation for the entire second-order lan-
can be reduced in a certain sense to the (global) consequence relation
guage �
over frames. More precisely, Thomason showed that there is a computable trans-
� sentences � to modal formulas � ���, and a special ﬁxed modal
lation � taking �

�

�

�
136

3 Frames

formula �, such that for all sets of of �

� sentences �, we have that

� �� � iff ��� � �� ��� � � � � �

�

�

� ����

On the frame level, propositional modal logic must be understood as a rather strong
fragment of classical monadic second-order logic. We now face the question: why?
The answer turns out to be surprisingly simple. Recall from Deﬁnition 3.1 that
validity is deﬁned by quantifying over all states of the universe and all possible
valuations. But a valuation assigns a subset of a frame to each proposition let-
ter, and this means that when we quantify across all valuations we are implicitly
quantifying across all subsets of the frame. In short, monadic second-order quan-
tiﬁcation is hard-wired into the very deﬁnition of validity; it is hardly surprising
that frame-deﬁnability is such a powerful concept.

Let’s make this answer more precise. In the previous chapter, we saw that at
�� � �� can be translated in a truth-
��� (see Proposition 2.47). Let us

the level of models, the modal language ��
preserving way into the ﬁrst-order language �
adopt a slightly different perspective:

�

�

View the predicate symbol � that corresponds to the propositional letter � as
a monadic second-order variable that we can quantify over.

If we do this, we are in effect viewing the standard translation as a way of translat-
��� introduced in Deﬁnition 3.4. And
ing into the second-order frame language �
if we view the standard translation this way we are lead, virtually immediately, to
the following result.

�

�

Proposition 3.12 Let � be a modal similarity type, and � a � -formula. Then for
any � -frame � and any state � in �:

�

� �

�

� iff �

� iff �

�

�

�� ��

� � � ��

�������

�

�

�

��

�� ��

� � � ��

��

����

�

�

�

��

Here, the second-order quantiﬁers bind second-order variables �
to the proposition letters �

occurring in �.

�

corresponding

Proof. Let �
Then we have that

� �

�

� � � be any model based on �, and let � be any state in �.

�

�

�

� � �� �

�

� iff �

��

��

������ �

� � � � � �

��

�

�

�

�

�

� � � � � �

���, and � ��

� means ‘assign � to the free ﬁrst-order variable
where the notation ��� �
� in ��
� to the free monadic second-order variables’.
Note that this equivalence is nothing new; it’s simply a restatement of Proposi-
tion 2.47 in second-order terms. But then we obtain the ﬁrst part of the Theorem
. The second
simply by universally quantifying over the free variables �

,. . . ,�

�� � � � � � ��

�

�

�

�

�

3.2 Frame Deﬁnability and Second-Order Logic

137

part follows from the ﬁrst by universally quantifying over the states of the frame
(as in Proposition 3.30). �

�

�

�

�

�

�

��

��

� � � ��

��� formula ��

It is fairly common to refer to the �
��� as the
standard translation of �, since it is usually clear whether we are working at the
level of models or the level of frames. Nonetheless, we will try and reserve the
term standard translation to mean the �
��� formula produced by the translation
��� as the second-order translation of �.
process, and refer to ��
Let’s sum up what we have learned. That modal formulas can deﬁne second-
order properties of frames is neither mysterious nor surprising: because modal
validity is deﬁned in terms of quantiﬁcation over subsets of frames, it is intrinsi-
cally second-order, hence so is the notion of frame deﬁnability. Indeed, the real
mystery lies not with such honest, hard-working, formulas as L¨ob and McKinsey,
but with such lazy formulas as T, 4 and 5 discussed in the previous section. For
example, if we apply the second-order translation to T (that is, � �
�) we obtain

� � � ��

��

��

�

�

�

�

�

�� �� �� � � ������ � � ����

We already know that T deﬁnes reﬂexivity, so this must be a (somewhat baroque)
second-order way of expressing reﬂexivity — and it’s fairly easy to see that this
is so. But this sort of thing happens a lot: 4 and 5 give rise to (fairly complex)
second-order expressions, yet the complexity melts away leaving a simple ﬁrst-
order equivalent behind. The contrast with the McKinsey formula is striking: what
is going on? This is an interesting question, and we discuss it in detail in Sec-
tions 3.5–3.7.

Another point is worth making: our discussion throws light on the somewhat
mysterious general frames introduced in Section 1.4. Recall that a general frame is
a frame together with a collection of valuations � satisfying certain modally natural
closure conditions. We claimed that general frames combined the key advantage
of frames (namely, that they support the key logical notion of validity) with the
advantage of models (namely, that they are concrete and easy to work with). The
work of this section helps explain why.

The key point is this. A general frame can be viewed as a generalized model
for (monadic) second-order logic. A generalized model for second-order logic is
a model in which the second-order quantiﬁers are viewed as ranging not over all
subsets, but only over a pre-selected sub-collection of subsets. And of course, the
collection of valuations � in a general frame is essentially such a sub-collection of
subsets. This means that the following equivalence holds:

�

�

� ��

�

� iff �

�

� �� �� ��

� � � ��

��

���

�

�

�

��

denotes not genuine second-order quan-
Here the block of quantiﬁers ��
tiﬁcation, but generalized second-order quantiﬁcation (that is, quantiﬁcation over

� � � ��

�

�

138

3 Frames

the subsets in �). Generalized second-order quantiﬁcation is essentially a ﬁrst-
order ‘approximation’ of second-order quantiﬁcation that possesses many proper-
ties that genuine second-order quantiﬁcation lacks (such as Completeness, Com-
pactness, and L¨owenheim-Skolem). In short, one of the reasons general frames
are so useful is that they offer a ﬁrst-order perspective (via generalized models) on
what is essentially a second-order phenomenon (frame validity). This isn’t the full
story — the algebraic perspective on general frames is vital to modal logic — but
it should make clear that these unusual looking structures ﬁll an important logical
niche.

Exercises for Section 3.2
3.2.1

(a) Consider a modal language with two diamonds ��� and ���. Prove that the
� is deﬁned by the
�.
(b) Conclude that in the similarity type of PDL, the set � as deﬁned in Example 3.10

� is the reﬂexive transitive closure of �
� and ���

class of frames in which �
conjunction of the formulas ���

� ������

� �����

� ���

� �

� �

�

�

�

�

�

�

�

deﬁnes the class of �-proper frames.

(c) Consider the example of multi-agent epistemic logic; let ��

� be the set of
agents. Suppose that one is interested in the operators � (� � stands for ‘everybody
knows �’) and � (� � meaning that ‘it is common knowledge that �’). The intended
relations modeling � and � are given by:

� � � � � �

�

��

�

�

��

�

iff
iff

�

��

�

�

�

�

�

�

there is a path �

�

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

� �

�

�

�

�

�

�

Write down a set of (epistemic) formulas that characterizes the class of epistemic
frames where these conditions are met.

3.2.2 Show that Grzegorczyk’s formula, �
of frames �
inﬁnite paths �

� � � � such that for all �, �

� characterizes the class
� satisfying (i) � is reﬂexive, (ii) � is transitive and (iii) there are no

��.

�

�

��

�

�� �

� �

� �

� �

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

3.2.3 Consider the basic temporal language (see Example 1.24). Recall that a frame �

�

�� �

� �

�

�

�

� for this language is called bidirectional if �

is the converse of �

.

�

�

(a) Prove that among the ﬁnite bidirectional frames, the formula �

�

��

�

��

�

� �

together with its converse, �
frames.

�

�

� �

� �

�

� � deﬁnes the transitive and irreﬂexive

(b) Prove that among the bidirectional frames that are transitive, irreﬂexive, and satisfy

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

�

��

�, this same set deﬁnes the ﬁnite frames.

(c) Is there a ﬁnite set of formulas in the basic modal language that has these same

deﬁnability properties?

3.2.4 Consider the following formula in the basic similarity type:

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

� �

�

� �

��

��

�

�

�

The aim of this exercise is to show that � does not deﬁne a ﬁrst-order condition on frames.

3.3 Deﬁnable and Undeﬁnable Properties

139

(a) To obtain some intuitions about the meaning of �, let us ﬁrst give a relatively simple

ﬁrst-order condition implying the validity of �:

�

��

���

�

���

��

���

���

�

�

���

�

�� �

�

� �

�

� �

��

�

� � �

�

�

����

stating (in words) that for every pair �
has at most one successor, this point being also a successor of �.
Show that � is valid in any frame satisfying �.

�� �

� in �, � has a successor � which itself

(b) Consider the frame �

� which we deﬁne as follows. Let � be a non-
principal ultraﬁlter over the set � of the natural numbers. Then �
�,
that is, the states of � are � itself, each subset of � that is a member of � and each
natural number. The relation � is the converse of the membership relation, that is,
�.
��� iff �

�. Show that �

� and �

�� �

�� �

� �

� �

�

�

�

�

�

�

(c) Prove that � does not have a ﬁrst-order correspondent by showing that � is in-
valid on all countable structures that are elementarily equivalent to � (that is, all
countable structures satisfying the same ﬁrst-order formulas as �).

3.3 Deﬁnable and Undeﬁnable Properties

We have seen that modal languages are a powerful tool for deﬁning frames: we
have seen examples of modally deﬁnable frame classes that are not ﬁrst-order de-
ﬁnable, and it is clear that validity is an inherently second-order concept. But what
are the limits of modal deﬁnability? For example, can modal languages deﬁne all
ﬁrst-order frame classes (the answer is no, as we will shortly see)? And anyway,
how should we go about showing that a class of frames is not modally deﬁnable?
After all, we can’t try out all possible formulas; something more sophisticated is
needed.

In this section we will answer these question by introducing four fundamental
frame constructions: disjoint unions, generated subframes, bounded morphic im-
ages, and ultraﬁlter extensions. The names should be familiar: these are the frame
theoretic analogs of the model-theoretic constructions studied in the previous chap-
ter, and they are going to do a lot of work for us, both here and in later chapters.
For a start, it is a more-or-less immediate consequence of the previous chapter’s
work that the ﬁrst three constructions preserve modal validity, while the fourth
anti-preserves it. But this means that these constructions provide powerful tests for
modal deﬁnability: by showing that some class of frames is not closed under one
of these constructions, we will be able to show that it cannot be modally deﬁnable.

Deﬁnition 3.13 The deﬁnitions of the disjoint union of a family of frames, a gen-
erated subframe of a frame, and a bounded morphism from one frame to another,
are obtained by deleting the clauses concerning valuations from Examples 2.2, 2.5
and 2.10.

That is, for disjoint � -frames �

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

such that � is the union of the sets �

(� � �), their disjoint union is
and for

�

the structure
each �

� � , �

�

�

�

�

�

�

�

� ��� �

�

�

� is the union

.

�

�

�

�

�

�

�

�
140

3 Frames

We say that a � -frame �

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

� ��� �

�

�

�

(notation: �

�

�

�) whenever �

is a generated subframe of the frame
� is a subframe of � (with respect

to �

� for all �

� � ), and the following heredity condition is fulﬁlled for all �

� �

if � � �

� and �

�

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

the subframe gen-
Let � be a subset of the universe of a frame �; we denote by �
erated by �, that is, the generated subframe of � that is based on the smallest set
� that contains � and satisﬁes the above heredity condition. If � is a singleton
for the subframe generated by �; if a frame � is generated by a

���, we write �
singleton subset of its universe, we call it rooted or point-generated.

�

�

�

And ﬁnally, a bounded morphism from a � -frame �

�

frame �
conditions:

� ��

�

�

� �

� �

�

�

�

is a function from � to �

to a � -
� satisfying the following two

� ��� �

�

�

�

�

�

(forth) For all �
(back) If �

�

�

� � , �

�

��

�

�

� � � �

implies �
then there exist �

�

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

such that �

�

� � � �

��

� � � �

and

� ��

� � �

�

�

�

(for � � � � �).

�

�

�

�

�

�

We say that �
surjective bounded morphism from � onto �

� is a bounded morphic image of �, notation: �

�. �

�, if there is a

�

�

It is an essential characteristic of modal formulas that their validity is preserved
under the structural operations just deﬁned:

Theorem 3.14 Let � be a modal similarity type, and � a � -formula.

� � � � � be a family of frames. Then

�

�

�

�

� if �

� for every �

�

�

�

(i) Let �
in �.

(ii) Assume that �
(iii) Assume that �

�

�. Then �
�. Then �

�

�

� if �
� if �

�

�

�.
�.

�

�

�

�

�

�

Proof. We only prove (iii), the preservation result for taking bounded morphic
images, and leave the other cases to the reader as Exercise 3.3.1. So, assume that �
is a surjective bounded morphism from � onto �
�. We have to show
�. Then there must be a valuation �
that �
�. Deﬁne the following valuation � on �:
and a state �

�. So suppose that � is not valid in �

� such that �

�, and that �

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

� ��

� � �� � � � � ��� � �

��

���

�

�

�

�

�

�

�

�

� � � and �

This deﬁnition is tailored to make � a bounded morphism between the models
� — the reader is asked to verify the details. Now we use the
�. It follows from Proposi-
�. In other words, we have falsiﬁed � in the frame �,

fact that � is surjective to ﬁnd a � such that � ��� � �
tion 2.14 that �
and shown the contrapositive of the desired result. �

� � �� � �

� �

�

�

�
3.3 Deﬁnable and Undeﬁnable Properties

141

Think of these frame constructions as test criteria for the deﬁnability of frame
properties: if a property is not preserved under one (or more) of these frame con-
structions, then it cannot be modally deﬁnable. Let’s consider some examples of
such testing.

Example 3.15 The class of ﬁnite frames is not modally deﬁnable. For suppose
there was a set of formulas � (in the basic modal similarity type) characteriz-
ing the ﬁnite frames. Then � would be valid in every one-point frame �

�

�

���

�� ���

� �

�

�

�

��� (� � �). By Theorem 3.14(1) this would imply that � was

also valid in the disjoint union

:

�

�

�

�

�

�

�

�

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

��

��

��

��

�

�

But clearly this cannot be the case, for

is inﬁnite.

�

�

�

The class of frames having a reﬂexive point (�� ���) does not have a modal
characterization either (again we work with the basic modal similarity type). For
suppose that the set � characterized this class. Consider the following frame �:

�

�

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

As � is a reﬂexive state, �
�. Now consider the generated subframe �
of �.
, since neither � nor � is reﬂexive. But this contra-
Clearly, � cannot be valid in �
dicts the fact that validity of modal formulas is preserved under taking generated
subframes (Theorem 3.14(ii)).

�

�

�

The two ﬁnal examples involve the use of bounded morphisms. First, irreﬂexiv-
ity is not deﬁnable. To see this, simply note that the function which collapses the
set of natural numbers in their usual order to a single reﬂexive point is a surjec-
tive bounded morphism. As the former frame is irreﬂexive, while the latter is not,
irreﬂexivity cannot be modally deﬁnable.

Actually, a more sophisticated variant of this example lets us prove even more.
� �� � � �, the natural numbers with the
� ���� ��� ���� ��� ��� ���� as

Consider the following two frames: �
successor relation (��� iff � � � � �), and �
depicted below.

142

3 Frames

�

�

�

�

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

In Example 2.11 we saw that the map � sending even numbers to � and odd num-
bers to � is a surjective bounded morphism. By the same style of reasoning as in
the earlier examples, it follows that no property � is modally deﬁnable if � has �
and � lacks it. This shows, for example, that there is no set of formulas character-
izing the asymmetric frames (��� ���� � ����)). �

�

Now for the fourth frame construction. Recall that in Section 2.5 we introduced
the idea of ultraﬁlter extensions; see Deﬁnition 2.57 and Proposition 2.59. Once
again, simply by ignoring the parts of the deﬁnition that deal with valuations, we
can lift this concept to the level of frames, and this immediately provides us with
the following anti-preservation result:

Corollary 3.16 Let � be a modal similarity type, � a � -frame, and � a � -formula.
Then �

� if �� �

�.

�

�

Proof. Assume that � is not valid in �. That is, there is a valuation � and a state �
such that �
in the ultraﬁlter
extension of �. But then we have refuted � in �� �. �

��. By Proposition 2.59, �� is false at �

� � �� �

�

�

�

Once again, we can use this result to show that frame properties are not modally
deﬁnable. For example, working in the basic modal similarity type, consider the
property that every state has a reﬂexive successor: ���� ���� � ����. We claim
that this property is not modally deﬁnable, even though it is preserved under taking
disjoint unions, generated subframes and bounded morphic images. To verify our
It is easy to
claim, the reader is asked to consider the frame in Example 2.58.
see that every state of �� � has a reﬂexive successor — take any non-principal
ultraﬁlter. But � itself clearly does not satisfy the property, as � has no reﬂexive
states. Now suppose that the property were modally deﬁnable, say by the set of
� — a clear violation of
formulas �. Then we would have �� �
Corollary 3.16.

�, but �

�

�

Note the direction of the preservation result in Corollary 3.16.

It states that
modal validity is anti-preserved under taking ultraﬁlter extensions. This naturally
raises the question whether the other direction holds as well, that is, whether �

�

�

�
3.3 Deﬁnable and Undeﬁnable Properties

143

�. For a partial answer to this question, we need the following

�

implies �� �
theorem:

Theorem 3.17 Let � be a modal similarity type, and � a � -frame. Then � has an
ultrapower

�� �. In a diagram:

� such that

�

�

�

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

�� �

Proof. Advanced track readers will be asked to supply a proof of this Theorem in
Exercise 3.8.1 below. �

And now we have the following partial converse to Corollary 3.16:

Corollary 3.18 Let � be a modal similarity type, and � a � -formula. If � deﬁnes
a ﬁrst-order property of frames, then frame validity of � is preserved under taking
ultraﬁlter extensions.

Proof. Let � be a modal formula which deﬁnes a ﬁrst-order property of frames, and
�. By the previous theorem, there is an ultrapower
let � be a frame such that �
�� �. As ﬁrst-order properties are preserved under

� of � such that

�

�

�

�

�

taking ultrapowers,

�

�

�

�

�

�. But then �� �

�

� by Theorem 3.14. �

�

We are on the verge of one of the best-known results in modal logic: the Goldblatt-
Thomason Theorem. This result tells us that — at least as far as ﬁrst-order deﬁnable
frame classes are concerned — the four frame constructions we have discussed
constitute necessary and sufﬁcient conditions for a class of frames to be modally
deﬁnable. We are not going to prove this important result right away, but we will
take this opportunity to state it precisely. We use the following terminology: a class
of frames � reﬂects ultraﬁlter extensions if �� �

� implies �

�.

�

�

Theorem 3.19 (Goldblatt-Thomason Theorem) Let � be a modal similarity type.
A ﬁrst-order deﬁnable class � of � -frames is modally deﬁnable if and only if it
is closed under taking bounded morphic images, generated subframes, disjoint
unions and reﬂects ultraﬁlter extensions.

Proof. A model-theoretic proof will be given in Section 3.8 below; this proof lies
on the advanced track. An algebraic proof will be given in Chapter 5; this proof
lies on the basic track. In addition, a simple special case which holds for ﬁnite
transitive frames is proved in the following section. �

In fact, we can weaken the condition of ﬁrst-order deﬁnability to closure under
ultrapowers, cf. Exercise 3.8.4 or Theorem 5.54.

144

3 Frames

Exercises for Section 3.3
3.3.1

(a) Prove that frame validity is preserved under taking generated subframes and

disjoint unions.

(b) Which of the implications in Theorem 3.14 can be replaced with an equivalence?
(c) Is frame validity preserved under taking ultraproducts?

3.3.2 Consider the basic modal language. Show that the following properties of frames
are not modally deﬁnable:

�

�

�

�

�

��

���

���

��,
��,

(a) antisymmetry (�
(b) �
(c) �
(d) acyclicity (there is no path from any � to itself),
(e) every state has at most one predecessor,
(f) every state has at least two successors.

�),

�

�

��

�

�

�

�

3.3.3 Consider a language with three diamonds, �
�. For each of the frame
conditions on the corresponding accessibility relations below, ﬁnd out whether it is modally
deﬁnable or not.

� and �

�, �

(a) �
(b) �
(c) �
(d) �
(e) �
(f) �

� and �

� is the union of �
� is the intersection of �
� is the complement of �
� is the composition of �
� is the identity relation,
� is the complement of the identity relation.

�,
� and �
�,
� and �

�,

�,

3.3.4 Show that any frame is a bounded morphic image of the disjoint union of its rooted
generated subframes.

3.4 Finite Frames
In this section we prove two simple results about ﬁnite frames. First we state and
prove a version of the Goldblatt-Thomason Theorem for ﬁnite transitive frames.
Next we introduce the ﬁnite frame property, and show that a normal modal logic
has the ﬁnite frame property if and only if it has the ﬁnite model property.

Finite transitive frames
An elegant analog of the Goldblatt-Thomason Theorem holds for ﬁnite transitive
frames: within this class, closure under the three structural operations of (ﬁnite)
disjoint unions, generated submodels, and bounded morphisms is a necessary and
sufﬁcient condition for a class of frames to be modally deﬁnable. The proof is
straightforward and makes use of Jankov-Fine formulas.

Let �

� ��� �� be a point-generated ﬁnite transitive frame for the basic modal
similarity type, and let � be a root of �. The Jankov-Fine formula �
is essen-
tially a description of � that has the following property: it is satisﬁable on a frame
� if and only if � is a bounded morphic image of a generated subframe of �.

��

�

3.4 Finite Frames

145

We build Jankov-Fine formulas as follows. Enumerate the states of � as �
, where � � �

, . . . ,
.
with a distinct proposition letter �

. Associate each state �
be the conjunction of the following formulas:

�

�

�

�

�

�

Let �

�

��

�

(i) �
(ii) �
(iii) ��
(iv) ��
(v) ��

�

�

� � � � � �

�.

��

�

�

� ��

� �

��

� ��

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

�, for each �� � with � �� � � �
�, for each �� � with ��

�

�

�

�

�

�

� �

�

� �

��

� �

�

�

�

�

�, for each �� � with ���

�

�

�

�

�

�

�

Note that as � is transitive, each node in � is accessible in one step from �. It fol-
� are satisﬁed at �, � is true throughout
lows that when formulas of the form � �
�. With this observed, the content of Jankov-Fine formulas should be clear: the
(with
ﬁrst three conjuncts state that each node in � is uniquely labeled by some �
) while the last two conjuncts use this labeling to describe the frame

labelling �

�

�

�

�

�

structure.

Lemma 3.20 Let � be a transitive, ﬁnite, point-generated frame, let � be a root
of �, and let �
be the Jankov-Fine formula for � and �. Then for any frame �
we have the following equivalence: there is a valuation � and a node � such that

��

�

�

�

�

� � �� �

�

�

��

if and only if there exists a bounded morphism from �

onto �.

�

Proof. Left to the reader as Exercise 3.4.1. �

With the help of this lemma, it is easy to prove the following Goldblatt-Thomason
analog:

denotes the basic modal similarity type. Let � be a
Theorem 3.21 Recall that �
-frames. Then � is deﬁnable within the class of transitive ﬁnite � -frames
class of �
if and only if it is closed under taking (ﬁnite) disjoint unions, generated subframes,
and bounded morphic images.

�

�

Proof. The right to left direction is immediate: we know from the previous section
that any modally deﬁnable frame class is closed under these operations. So let’s
consider the more interesting converse.

that is, �

Assume that � satisﬁes the stated closure condition. Let �
�. We will show that �

� be the logic of �;
� deﬁnes �. Clearly
� is valid on every frame in �, so to complete the proof we need to show that if
�. We split the proof into two

�, where � is ﬁnite and transitive, then �

�, for all �

�

�

� �� �

�

�

�

�

�

�

�

�

cases.

First suppose that � is point-generated with root �. Consider the Jankov-Fine
�.
; in other words, for some
. Thus by the previous lemma,

formula �
Hence there is some �
valuation � and state � we have �

is satisﬁable in � at �, so ��

for � and �. Clearly �

� such that �

� � �� �

�� �

��

��

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

��

�
146

3 Frames

� is a bounded morphic image of the point-generated subframe �
closure conditions on �, it follows that �

�.

�

�

of �. By the

So suppose that � is not point-generated. But then as �

�, so does each
point-generated subframe of �, hence by the work of the previous paragraph all
these subframes belong to �. But by Exercise 3.3.4, � is a bounded morphic image
of the disjoint union of its rooted generated subframes, so � belongs to � too. �

�

�

The ﬁnite frame property

Our next result deals not with frame deﬁnability, but with the relationship between
normal modal logics and ﬁnite frames. Normal modal logics were introduced in
Section 1.6 (see in particular Deﬁnition 1.42). Recall that normal modal logics
are sets of formulas (containing certain axioms) that are closed under three simple
conditions (modus ponens, uniform substitution, and generalization). They are the
standard tool for capturing the notion of validity syntactically.

Now, in Section 2.3 we introduced the ﬁnite model property. We did not apply
the concept to normal modal logics — but as a normal logic is simply a set of
formulas, we can easily extend the deﬁnition to permit this:

Deﬁnition 3.22 A normal modal logic � has the ﬁnite model property with respect
� and every formula not in � is refuted in a ﬁnite
to some class of models � if �
model � in �. � has the ﬁnite model property if it has the ﬁnite model property
with respect to some class of models. �

�

Informally, if a normal modal logic has the ﬁnite model property, it has a ﬁnite
semantic characterization: it is precisely the set of formulas that some collection of
ﬁnite models makes globally true. This is an attractive property, and as we’ll see in
Chapter 6 when we discuss the decidability of normal logics, a useful one too.

But something seems wrong. It is the level of frames, rather than the level of
models, which supports the key logical concept of validity. It certainly seems sen-
sible to try and semantically characterize normal logics in terms of ﬁnite structures
— but it seems we should do so using ﬁnite frames, not ﬁnite models. That is, the
following property seems more appropriate:

Deﬁnition 3.23 (Finite Frame Property) Let � be a normal modal logic and F a
class of ﬁnite frames. We say � has the ﬁnite frame property with respect to F if
and only if �
such that � is falsiﬁable on �. We say � has the ﬁnite frame property if and only if
it has the ﬁnite frame property with respect to some class of ﬁnite frames. �

�, and for every formula � such that � �� � there is some �

�

�

�

Note that to establish the ﬁnite frame property of a normal modal logic �, it is not
sufﬁcient to prove that any formula � �� � can be refuted on a model where � is

3.4 Finite Frames

147

globally true: in addition one has to ensure that the underlying frame of the model
validates �. If a logic has the ﬁnite frame property (and many important ones do,
as we will learn in Chapter 6) then clearly there is no room for argument: it really
can be characterized semantically in terms of ﬁnite structures.

But now for a surprising result. The ﬁnite frame property is not stronger than the
ﬁnite model property: we will show that a normal modal logic has the ﬁnite frame
property if and only if it has the ﬁnite model property. This result will prove useful
at a number of places in Chapters 4 and 6. Moreover, while proving it we’ll meet
some other concepts, notably deﬁnable variants and distinguishing models, which
will be useful when proving Bull’s Theorem in Section 4.9.

Deﬁnition 3.24 (Deﬁnable Variant) Let �
We say � is deﬁnable in � if and only if there is a formula �
states � � � , �
iff � � � .
Any model �

� �

�

�

�

� ��� �� � � be a model and � � � .
such that for all

�

� based on the frame ��� �� is called a variant of �. A variant
� of � is deﬁnable in � if and only if for all proposition symbols �,
� is a variant of � that is deﬁnable in �, we call �

�

��� �� �

�

�

�

��� is deﬁnable in �. If �
a deﬁnable variant of �. �

Recall that normal modal logics are closed under uniform substitution, the process
of uniformly replacing propositional symbols with arbitrary formulas (see Sec-
tion 1.6), and that a formula obtained from � by uniform substitution is called a
substitution instance of �. Our intuitive understanding of uniform substitution suf-
ﬁces for most purposes, but in order to prove the following lemma we need to refer
to the precise concepts of Deﬁnition 1.18.

Lemma 3.25 Let �
ant of �. For any formula �, let �
symbol � in � by �
, where �
�, and all normal modal logics �:

� �

�

�

�

�

�

�

� � � be a model and �

�

� be a deﬁnable vari-
� be the result of uniformly replacing each atomic
��� in �. Then for all formulas

deﬁnes �

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

(i) �
(ii) If every substitution instance of � is true in �, then every substitution in-

� iff �

� �

� �

�

�

�

�

�

�.
stance of � is true in �
�.
� then �

�

�

�

(iii) If �

Proof. Item (i) follows by induction on �. For the base case we have �
. As ����
� iff �
(cf. Deﬁnition 1.18) the inductive steps are immediate.

�, �� � ��

�, and �

� ��

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

� �

�

�

�

�

�

For item (ii), we show the contrapositive. Let � be a substitution instance of �
�. By
� is a substitution instance

�. Thus there is some � in � such that �

and suppose that �
item (i), �

�, which means that �

�. But as �

� � �

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
148

3 Frames

of �, and � is a substitution instance of �, we have that �
of � (see Exercise 1.2.5) and the result follows.

� is a substitution instance

Item (iii) is an immediate consequence of item (ii), for normal modal logics are

closed under uniform substitution. �

We now isolate a type of model capable of deﬁning all its variants:

Deﬁnition 3.26 (Distinguishing Model) A model � is distinguishing if the rela-
tion � of modal equivalence between states of � is the identity relation. �

In other words, a model � is distinguishing if and only if for all states � and �
in �, if � �� �, then there is a formula � such that �
�.
Many important models are distinguishing. For example, all ﬁltrations (see Deﬁ-
nition 2.36) are distinguishing. Moreover, the canonical models introduced in Sec-
tion 4.2 are distinguishing too. And, and as we will now see, when a distinguishing
model is ﬁnite, it can deﬁne all its variants.

� and �

� � �

� �

�

�

Lemma 3.27 Let �

� � � be a ﬁnite distinguishing model. Then:

� �

�

(i) For every state � in � there is a formula �
(ii) � can deﬁne any subset of �. Hence � can deﬁne all its variants.
(iii) If �

� then �

�.

that is true at, and only at, �.

�

�

�

Proof. For item (i), suppose that �

,. . . ,�

�

�

�

. For all pairs ��� � � such that � � �� � � � and � �� �, choose �

� ��� ��, and enumerate the states in � as
to be a
(such a formula exists, for � is
and

is true at �

� Clearly �

� � � � � �

� �

���

���

�

�

�

�

��

�

���

�

�

�

�

formula such that �
distinguishing) and deﬁne �
false everywhere else.

� �

�

�

�

���

and �
to be �

Item (ii) is an easy consequence. For let � be any subset of � . Then

�

�

deﬁnes � . Hence as � can deﬁne all subsets of � , it can deﬁne �
valuation �

� on � and propositional symbol �.

�

�

�

�

���, for any

�

As for item (iii), suppose �
�, where �

�. By item (iii) of the previous lemma we have
� is any deﬁnable variant of �. But we have just seen that

�

�

that �
� can deﬁne all its variants, hence �

�

�. �

�

Lemmas 3.25 and 3.27 will be important in their own right when we prove Bull’s
theorem in Section 4.9. And with the help of a neat ﬁltration argument, they yield
the main result:

Theorem 3.28 A normal modal logic has the ﬁnite frame property iff it has the
ﬁnite model property.

Proof. The left to right direction is immediate. For the converse, suppose that �
is a normal modal logic with the ﬁnite model property. Since we will need to take

�
3.4 Finite Frames

149

a ﬁltration through �, we have to be explicit about the set of proposition letters of
the formulas in �, so assume that � �
Take a formula in the language ��

�� � ��.

����

�� � �� that does not belong to �. We will
�.

�

show that � can be refuted on a ﬁnite frame � such that �

As � has the ﬁnite model property, there is a ﬁnite model � such that �

�

�

�

� � �

� . As �

and �
formulas in ��� � �, and let �
so is �
Theorem (Theorem 2.39), �
in � satisﬁes all formulas in �, so does every state in �
from the Filtration Theorem). Let � be the (ﬁnite) frame underlying �
Lemma 3.27 item (iii), �

� for some state � in �. Let � be the set of all subformulas of
� be any ﬁltration of � through �. As � is ﬁnite,
� is a ﬁltration, it is a distinguishing model. By the Filtration
�, for as every state
� (again, this follows
� . By

�, and we have proved the theorem. �

�. Moreover �

� ��� �

�

�

�

�

�

Note the somewhat unusual use of ﬁltrations in this proof. Normally we ﬁltrate
inﬁnite models through ﬁnite sets of formulas. Here we ﬁltrated a ﬁnite model
through an inﬁnite sets of formulas to guarantee that an entire logic remained true.
This result shows that the concepts of normal modal logics and frame valid-
ity ﬁt together well in the ﬁnite domain: if a normal logic has a ﬁnite semantic
characterization in terms of models, then it is guaranteed to have a ﬁnite frame-
based semantic characterization as well. But be warned: one of the most striking
results of the following chapter is that logics and frame validity don’t always ﬁt
together so neatly. In fact, the frame incompleteness results will eventually lead
us (in Chapter 5) to the use of new semantic structures, namely modal algebras, to
analyze normal modal logics. But this is jumping ahead. It’s time to revert to our
discussion of frame deﬁnability — but from a rather different perspective. So far,
our approach has been ﬁrmly semantical. This has taught us a lot: in particular,
the Goldblatt-Thomason theorem has given us a model-theoretic characterization
of the elementary frame classes that are modally deﬁnable. Moreover, we will see
in Chapter 5 that the semantic approach has an important algebraic dimension. But
it is also possible to approach frame deﬁnability from a more syntactic perspective,
and that’s what we’re going to do now. This will lead us to the other main result of
the chapter: the Sahlqvist Correspondence Theorem.

Exercises for Section 3.4
3.4.1 Prove Lemma 3.20. That is, suppose that �
transitive ﬁnite frame � with root �. Show that for any frame �, �
at a node � iff � is a bounded morphic image of �

.

��

�

is the Jankov-Fine formula for a
is satisﬁable on �

�

��

3.4.2 Let � be a model, let �
� be any ﬁltration of � through some ﬁnite set of formulas
�, and let � be the natural map associated with the ﬁltration. If � is a point in the ﬁltration,
show that �

� is deﬁnable in �.

�

�

�

�

�

150

3 Frames

3.5 Automatic First-Order Correspondence
We have learned a lot about frame deﬁnability in the previous sections. In partic-
ular, we have learned that frame deﬁnability is a second-order notion, and that the
second-order correspondent of any modal formula can be straightforwardly com-
puted using the Second-Order Translation. Moreover, we know that many modal
formulas have ﬁrst-order correspondents, and that the Goldblatt-Thomason Theo-
rem gives us a model-theoretic characterization of the frame classes they deﬁne.

Nonetheless, there remains a gap in our understanding: although many modal
formulas deﬁne ﬁrst-order conditions on frames, it is not really clear why they do
so. To put it another way, in many cases the (often difﬁcult to decipher) second-
order condition yielded by the second-order translation is equivalent to a much
simpler ﬁrst-order condition. Is there any system to this? Better, are there algo-
rithms that enable us to compute ﬁrst-order correspondents automatically, and if so,
how general are these algorithms? This section, and the two that follow, develop
some answers.

A large part of this work centers on a beautiful positive result: there is a large
class of formulas, the Sahlqvist formulas, each of which deﬁnes a ﬁrst-order con-
dition on frames which is effectively calculable using the Sahlqvist-van Benthem
algorithm; this is the celebrated Sahlqvist Correspondence Theorem, which we
will state and prove in the following section. The proof of this theorem sheds light
on why so many second-order correspondents turn out to be equivalent to a ﬁrst-
order condition. Moreover each Sahlqvist formula is complete with respect to the
class of ﬁrst-order frames it deﬁnes; this is the Sahlqvist Completeness Theorem,
which we will formulate more precisely in Theorem 4.42 and prove in Section 5.6.
All in all, the Sahlqvist fragment is interesting from both theoretical and practical
perspectives, and we devote a lot of attention to it.

In this section we lay the groundwork for the proof of the Sahlqvist Correspon-
dence Theorem. We are going to introduce two simple classes of modal formulas,
the closed formulas and the uniform formulas, and show that they deﬁne ﬁrst-order
conditions on frames. Along the way we are going to learn about positive and
negative formulas, what they have to do with monotonicity, and how they can help
us get rid of second-order quantiﬁers. These ideas will be put to work, in a more
sophisticated way, in the following section.

One other thing: in what follows we are going to work with a stronger notion of
correspondence. The concept of correspondence given in Deﬁnition 3.5 is global:
a modal and a (ﬁrst- or second-order) frame formula are called correspondents if
they are valid on precisely the same frames. But it is natural to demand that validity
matches locally:

Deﬁnition 3.29 (Local Frame Correspondence) Let � be a modal formula in
some similarity type, and ���� a formula in the corresponding ﬁrst- or second-

3.5 Automatic First-Order Correspondence

151

order frame language (� is supposed to be the only free variable of �). Then we
say that � and ���� are local frame correspondents of each other if the following
holds, for any frame � and any state � of �:

�

� �

�

� iff �

�� ����� �

�

In fact, we’ve been implicitly using local correspondence all along. In Example 3.6
� corresponds to ����� — but inspection of the proof
we showed that � �
� locally corresponds to ���. Similarly,
reveals we did so by showing that � �
� corresponds to density by showing
in Example 3.7 we showed that �
� locally corresponds to ��� ���� � ��� � ��� �. It should be
that �
clear from these examples that the local notion of correspondence is fundamental,
and that the following connection holds between the local and global notions:

� �

� �

��

��

�

Proposition 3.30 If ���� is a local correspondent of the modal formula �, then
�� ���� is a global correspondent of �. So if � has a ﬁrst-order local correspon-
dent, then it also has a ﬁrst-order global correspondent.

Proof. Trivial. �

What about the converse? In particular, suppose that the modal formula � has a
ﬁrst order global correspondent; will it also have a ﬁrst-order local correspondent?
Intriguingly, the answer to this question is negative, as we will see in Example 3.57.
But until we come to this result, we won’t mention global correspondence much:
it’s simpler to state and prove results in terms of local correspondence, relying on
the previous lemma to guarantee correspondence in the global sense. With this
point settled, it’s time to start thinking about correspondence theory systematically.

Closed formulas

There is one obvious class of modal formulas guaranteed to correspond to ﬁrst-
order frame conditions: formulas which contain no proposition letters.

Example 3.31 Consider the basic temporal language. The formula �
the property that there is no ﬁrst point of time. More precisely, �
precisely those frames such that every point has a predecessor.

� deﬁnes
� is valid on

Now, obviously it is easy to prove this directly, but for present purposes the
following argument is more interesting. By Proposition 3.12, for any bidirectional
frame � and any point � in � we have that:

�

� �

� �

� iff �

�� ��

� � � ��

�

������

�

�

�

��

�

where �

, . . . , �

are the unary predicate variables corresponding to the proposi-

�

�

152

3 Frames

occurring in �
tion letters �
ables, hence there are no second-order quantiﬁers, and hence:

�. But �

, . . . , �

�

�

� contains no propositional vari-

�

� �

� �

� iff �

��

�

��

�

������

�

But ��
corresponds to �� ��� (and thus globally corresponds to ���� ���). �

�� is �� ���� � � � ��, which is equivalent to �� ���. So �

�

�

�

� locally

The argument used in this example is extremely simple, and obviously general-
izes. We’ll state and prove the required generalization, and then move on to richer
pastures.

Deﬁnition 3.32 A modal formula � is closed if and only if it contains no proposi-
tion letters. Thus closed formulas are built up from �, �, and any nullary modali-
ties (or modal constants) the signature may contain. �

Proposition 3.33 Let � be a closed formula. Then � locally corresponds to a ﬁrst-
order formula �

��� which is effectively computable from �.

�

Proof. By Proposition 3.12 and the fact that � contains no propositional variables
we have:

�

� �

�

� iff �

��

��

�������

�

As it is easy to write a program that computes ��
ately. �

���, the claim follows immedi-

�

Closed formulas arise naturally in some applications (a noteworthy example is
provability logic), thus the preceding result is quite useful in practice.

Uniform formulas

Although the previous proposition was extremely simple, it does point the way to
the strategy followed in our approach to the Sahlqvist Correspondence Theorem:
we are going to look for ways of stripping off the initial block of monadic second-
���, thus reducing the translation to
order universal quantiﬁers in ��
���. The obvious way of getting rid of universal quantiﬁers is to perform
universal instantiation, and this is exactly what we will do. Both here, and in the
,
work of the next section, we will look for simple instantiations for the �
which result in ﬁrst-order formulas equivalent to the original. We will be able to
make this strategy work because of the syntactic restrictions placed on �.

, . . . , �

� � � ��

��

��

�

�

�

�

�

�

One of the restrictions imposed on Sahlqvist formulas invokes the idea of pos-
itive and negative occurrences of proposition letters. We now introduce this idea,
study its semantic signiﬁcance, and then, as an introduction to the techniques of

3.5 Automatic First-Order Correspondence

153

the following section, use a simple instantiation argument to show that the second-
order translations of uniform formulas are effectively reducible to ﬁrst-order con-
ditions on frames.

Deﬁnition 3.34 An occurrence of a proposition letter � is a positive occurrence if
it is in the scope of an even number of negation signs; it is a negative occurrence if
it is in the scope of an odd number of negation signs. (This is one of the few places
in the book where it is important to think in terms of the primitive connectives.
�� � �� is negative, for this formula is
For example, the occurrence of � in �
��� � ��.) A modal formula � is positive in � (negative in �) if all
shorthand for �
occurrences of � in � are positive (negative). A formula is called positive (negative)
if it is positive (negative) in all proposition letters occurring in it.

Analogous concepts are deﬁned for the corresponding second-order language.
That is, an occurrence of a unary predicate variable � in a second-order formula is
positive (negative) if it is in the scope of an even (odd) number of negation signs. A
second-order formula � is positive in � (negative in � ) if all occurrences of � in �
are positive (negative), and it is called positive (negative) if it is positive (negative)
in all unary predicate variables occurring in it. �

Lemma 3.35 Let � be a modal formula.

(i) � is positive in � iff ��

��� is positive in the corresponding unary predicate

�

� .

(ii) If � is positive (negative) in �, then �� is negative (positive) in �.

Proof. Virtually immediate. �

Positive and negative formulas are important because of their special semantic
properties. In particular, they exhibit a useful form of monotonicity.

�� � ��, and let � � �. A modal for-
Deﬁnition 3.36 Fix a modal language ��
mula � is upward monotone in � if its truth is preserved under extensions of
the interpretation of �. More precisely, � is upward monotone in � if for ev-
� such that
ery model ��� �

, every state � � � , and every valuation �

� � �

�

�

� ��� � �

�

��� and for all � �� �, � ��� � �

�

���, the following holds:

�

�

if ��� �

�

� � �

� �

�

�

�, then ��� �

�

�

� �

�

� �

�

�

�.

�

�

�

�

In short, extending � ��� (while leaving the interpretation of any other proposi-
tional variable unchanged) has the effect of extending � ��� (or keeping it the
same).

Likewise, a formula � is downward monotone in � if its truth is preserved under
,

shrinkings of the interpretation of �. That is, for every model ��� �

� � �

�

�

�

�

154

3 Frames

every state � � � , and every valuation �
���, the following holds:
� �� �, � ��� � �

�

� such that �

�

��� � � ��� and for all

if ��� �

�

� � �

� �

�

�

�, then ��� �

�

�

� �

�

� �

�

�

�.

�

�

�

�

The notions of a second-order formula being upward and downward monotone in
a unary predicate variable � are deﬁned analogously; we leave this task to the
reader. �

Lemma 3.37 Let � be a modal formula.

(i) If � is positive in �, then it is upward monotone in �.
(ii) If � is negative in �, then it is downward monotone in �.

Proof. Prove both parts simultaneously by induction on �; see Exercise 3.5.3. �

But what do upward and downward monotonicity have to do with frame deﬁnabil-
ity? The following example is instructive.

Example 3.38 The formula ��
�. Regardless of the valuation, the formula ��
suppose �
So consider a minimal valuation (for �) on �; that is, choose any �

� locally corresponds to a ﬁrst-order formula. For
� holds at �.
such that
�, there must be a successor � of � such that �

�

��� �

�

�. Then as �

�

��

��

� �

�

�

�

holds at �. However, there are no �-states, so � must be blind (that is, without
successors). In other words, we have shown that

�

�

� �

�� �

�

�

� only if �

��

�� �� ���� � ��� ��� �����

Now for the interesting direction: assume that the state � in the frame � has a
is any
�, where �
blind successor. It follows immediately that �
minimal valuation (for �). We claim that the formula ��
� is valid at �. To see this,
consider an arbitrary valuation � and a point � of �. By item (i) of Lemma 3.37,

��

�� �

� �

�

�

�

�

� is upward monotone in �. Hence it follows from the fact that �

��

�

��� � � ���

that �

�

� � �� �

�

��

�. As � was arbitrary, ��

� is valid on � at �. �

The key point is the last part of the argument: the use of a minimal valuation fol-
lowed by an appeal to monotonicity to establish a result about all valuations. But
now think about this argument from the perspective of the second-order correspon-
dence language: in effect, we instantiated the predicate variable corresponding to
� with the smallest subset of the frame possible, and then used a monotonicity
argument to establish a result about all assignments to � .

This simple idea lies behind much of our work on the Sahlqvist fragment. To
illustrate the style of argumentation it leads to, we will now use an instantiation
argument to show that all uniform modal formulas deﬁne ﬁrst-order conditions on
frames.

3.5 Automatic First-Order Correspondence

155

Deﬁnition 3.39 A proposition letter � occurs uniformly in a modal formula if it
occurs only positively, or only negatively. A predicate variable � occurs uniformly
in a second-order formula if it occurs only positively, or only negatively. A modal
formula is uniform if all the propositional letters it contains occur uniformly. A
second-order formula is uniform if all the unary predicate variables it contains
occur uniformly. �

Theorem 3.40 If � is a uniform modal formula, then � locally corresponds to a
ﬁrst-order formula �
is effectively computable from
�.

��� on frames. Moreover, �

�

�

Proof. Consider the universally quantiﬁed second-order equivalent of �:

��

� � � ��

����

�

�

�

��

(3.6)

�

�

, . . . , �

are second-order variables corresponding to the proposition let-
where �
ters in �. Our aim is to show that (3.6) is equivalent to a ﬁrst-order formula by per-
forming appropriate instantiations for the universally quantiﬁed monadic second-
order variables �

, . . . �

.

�

�

As � is uniform, by Lemma 3.35 so is ��

���. We will instantiate the unary
predicates that occur positively with a predicate denoting as small a set as possi-
ble (that is, the empty set), and the unary predicates that occur negatively with a
predicate denoting as large a set as possible (that is, all the states in the frame). We
will use Church’s �-notation for the required substitution instance providing the
formulas that deﬁne these predicates. For every � occurring in ��

���, deﬁne

�

��� � �

��� � �� ��

��� � � ��

�

�

if ��
if ��

�

�

��� is positive in �
��� is negative in � �

Of course, the idea is that instantiating a universal second-order formula according
to this substitution � simply means (i) removing the second-order quantiﬁers and
(ii) replacing every atomic subformula � � with the formula ��� ����, that is, with
either � �� � or � � � (as given by the deﬁnition).�

Now consider the following instance of (3.6) in which every unary predicate �

has been replaced by ��� �:

����

���

� � � � � ���

���

�

����

�

�

�

�

�

��

(3.7)

We will show that (3.7) is equivalent to (3.6). It is immediate that (3.6) implies
(3.7), for the latter is an instantiation of the former. For the converse implication
we assume that

�

�� ����

���

� � � � � ���

���

�

�������

�

�

�

�

�

��

(3.8)

� If you are unfamiliar with �-notation, all you really need to know to follow the proof is that ��� �

� and
� are predicates denoting the empty set and the set of all states respectively. Some explanatory

��� �

�

�

remarks on �-notation are given following the proof.

�
156

3 Frames

and we have to show that

�

��

�� ��

� � � ��

�������

�

�

�

�

���, we have that �

��� we
By the choice of ��� �, for predicates � that occur only positively in ��
�� �� ���� ���� � � ����, and for predicates � that occur only neg-
have that �
atively in ��
�� �� �� ��� � ��� �����. (Readers familiar
with �-notation will realize that we have implicitly appealed to �-conversion here.
Readers unfamiliar with �-notation should simply note that when ��� � is a predi-
cate denoting the empty set, then ��� ���� is false no matter what � denotes, while
if ��� � denotes the set of all states, ��� ���� is guaranteed to be true.) Hence,
��� is positive or negative in all unary predicates � occurring in it, (3.8)
as ��
together with Lemma 3.37 imply that for any choice of �

, . . . , �

,

�

�

�

��

�

� �

� � � � � �

� ��

�������

�

�

�

�

�

�

�� ��

� � � ��

��� as required. Finally, in any program-
which means that �
ming language with decent symbol manipulation facilities it is straightforward to
write a program which, when given a uniform formula �, produces ��
��� and
carries out the required instantiations. Hence the ﬁrst-order correspondents of uni-
form formulas are computable.

��

�

�

�

�

On �-notation
Although it is not essential to use �-notation, it is convenient and we will apply it
in the following section. For readers unfamiliar with it, here’s a quick introduction
to the fundamental ideas.

We have used Church’s �-notation as a way of writing predicates, that is, entities
which denote subsets. But lambda expressions don’t denote subsets directly; rather
they denote their characteristic functions. Suppose we are working with a frame
��� ��. Let � � � . Then the characteristic function of � (with respect to � ) is
��� � � if � � � and
the function �
is simply the function

��� � � otherwise. Reading 1 as true and 0 as false, �

with domain � and range ��� �� such that �

�

�

�

�

�

that says truthfully of each element of � whether it belongs to � or not.

Lambda expressions pick out characteristic functions in the obvious way. For
example, when working with a frame ��� ��, ��� � �� � denotes the function
from � to ��� �� that assigns 1 to every element � � � that satisﬁes � �� � and
0 to everything else. But for no choice of � is it the case that � �� �; hence, as
we stated in the previous proof, ��� � �� � denotes the characteristic function of
the empty set. Similarly, ��� � � � denotes the characteristic function of � , for
� � � for every � � � .

Lambda expressions take the drudgery out of dealing with substitutions. Con-
sider the second-order formula � �. This is satisﬁed in a model if and only if the

3.6 Sahlqvist Formulas

157

element assigned to � belongs to the subset assigned to � . For example, if � is as-
signed the empty set, � � will be false no matter what � is assigned. Now suppose
we substitute ���� � �� �� for � in � �. This yields the expression ���� � �� ���.
Read this as ‘apply the function denoted by ��� � �� � to the state denoted by �’.
Clearly this yields the value 0 (that is, false). The process of �-conversion men-
tioned in the proof is essentially a way of rewriting such functional applications
to simpler but equivalent forms; for more details, consult one of the introductions
cited in the Notes. Newcomers to �-notation should try Exercise 3.5.1 right away.

Exercises for Section 3.5
3.5.1 Explain why we could have used the following predicate deﬁnitions in the proof of
Theorem 3.38: for every � occurring in ��

�, deﬁne

�

�

�

�

�

�

� �

���

�

�

�

���

�

�

if ��
if ��

� is positive in �
� is negative in � �

�

�

�

�

�

�

If you have difﬁculties with this, consult one of the introductions to �-calculus cited in the
notes before proceeding further.

3.5.2 Let � be a modal formula which is positive in all propositional variables. Prove that
� can be rewritten into a normal form which is built up from proposition letters, using �,
�, � and � only.

3.5.3 Prove Lemma 3.37. That is, show that if a modal formula � is positive in �, then it
is upward monotone in �, and that if it is negative in �, then it is downward monotone in �.

3.6 Sahlqvist Formulas

In the proof of Theorem 3.40 we showed that uniform formulas correspond to ﬁrst-
order conditions by ﬁnding a suitable instantiation for the universally quantiﬁed
monadic second-order variables in their second-order translation and appealing to
monotonicity. This is an important idea, and the rest of this section is devoted to
extending it: the Sahlqvist fragment is essentially a large class of formulas to which
this style of argument can be applied.

Very simple Sahlqvist formulas

Roughly speaking, Sahlqvist formulas are built up from implications � � �,
where � is positive and � is of a restricted form (to be speciﬁed below) from which
the required instantiations can be read off. We now deﬁne a limited version of the
Sahlqvist fragment for the basic modal language; generalizations and extensions
will be discussed shortly.

158

3 Frames

Deﬁnition 3.41 We will work in the basic modal language. A very simple Sahl-
qvist antecedent over this language is a formula built up from �, � and proposi-
tion letters, using only � and �. A very simple Sahlqvist formula is an implication
� � � in which � is positive and � is a very simple Sahlqvist antecedent. �

Examples of very simple Sahlqvist formulas include � �

� and �� �

�

��

�� �

�� � ��.

��

The following theorem is central for understanding what Sahlqvist correspon-
Its proof describes and justiﬁes an algorithm for converting
dence is all about.
simple Sahlqvist formulas into ﬁrst-order formulas; the algorithms given later for
richer Sahlqvist fragments elaborate on ideas introduced here. Examples of the al-
gorithm in action are given below; it is a good idea to refer to these while studying
the proof.

Theorem 3.42 Let � � � � � be a very simple Sahlqvist formula in the basic
� ��. Then � locally corresponds to a ﬁrst-order formula
modal language ��

��

�

��� on frames. Moreover, �

is effectively computable from �.

�

�

�

Proof. Our starting point is the formula ��
����, which
is the local second-order translation of �. We assume that this translation has
undergone a pre-processing step to ensure that no two quantiﬁers bind the same
variable, and no quantiﬁer binds �. Let us denote ��
��� by POS; that is, we
have a translation of the form:

��� �

� � � ��

��

��

�

�

�

�

�

�

��

� � � ��

�

�

�

�

��

��� � POS��

(3.9)

We will now rewrite (3.9) to a form from which we can read off the instantiations
that will yield its ﬁrst-order equivalent.

Step 1. Pull out diamonds.
Use equivalences of the form

and

���

���

� � � � � ��

����

� � � �

�

�

�

�

���

���

� � � � � ��

����

� � � �

�

�

�

�

��� of (3.9)
(in that order) to move all existential quantiﬁers in the antecedent ��
to the front of the implication. Note that by our deﬁnition of Sahlqvist antecedents,
the existential quantiﬁers only have to cross conjunctions before they reach the
main implication. Of course, the above equivalences are not valid if the variable
occurs freely in �, but by our assumption on the pre-processing of the formula,

�

�

�

this problem does not arise.

Step 1 results in a formula of the form

��

� � � ��

��

� � � ��

�

�

�

�

�REL � AT � POS��

(3.10)

3.6 Sahlqvist Formulas

159

cor-
where REL is a conjunction of atomic ﬁrst-order statements of the form ��
responding to occurrences of diamonds, and AT is a conjunction of (translations of)
proposition letters. It may be helpful at this point to look at the concrete examples
given below.

�

�

�

Step 2. Read off instances.
We can assume that every unary predicate � that occurs in the consequent of the
matrix of (3.10), also occurs in the antecedent of the matrix of (3.10): otherwise
(3.10) is positive in � and we can substitute ��� � �� � for � (that is, make use of
the substitution used in the proof of Theorem 3.40) to obtain an equivalent formula
without occurrences of � .

Let �

�

be a unary predicate occurring in (3.10), and let �

�

� � � � � �

�

be all

�

�

�

�

�

�

the occurrences of the predicate �

in the antecedent of (3.10). Deﬁne

�

���

� � ��� �� � �

� � � � � � � �

��

�

�

�

�

�

�

, �

� is the minimal instance making the antecedent REL � AT true; this
Note that ���
, then � must be one of the
lambda expression says that if a node � has property �
in the antecedent. But
explicitly stated to have property �
nodes �
this is nothing else than saying that if some model � makes the formula AT true
under some assignment, then the interpretation of the predicate � must extend the
set of points where ��� � holds:

, . . . or �

�

�

�

�

�

�

�

�

�

�� �����

� � � �

� implies �

�� �� ����

���� � �

�����

� � � �

� (3.11)

�

�

�

�

�

�

This observation, in combination with the positivity of the consequent of the Sahl-
qvist formula, forms the key to understanding why Sahlqvist formulas have ﬁrst-
order correspondents.

Step 3. Instantiating.
We now use the formulas of the form ���
� for each occurrence of �
substitute ���
results in a formula of the form

�

�

�

� found in Step 2 as instantiations; we
in the ﬁrst-order matrix of (3.10). This

����

���

� � � � � ���

���

���

� � � ��

�

�

�

�

�

�

���� � AT � �����

Now, there are no occurrences of monadic second-order variables in REL. Further-
more, observe that by our choice of the substitution instances ��� �, the formula
�AT will be trivially true. So after carrying out these

� � � � � ���

����

���

���

�

�

�

�

substitutions we end up with a formula that is equivalent to one of the form

��

� � � ��

���� � ����

���

� � � � � ���

���

������

�

�

�

�

�

�

(3.12)

As we assumed that every unary predicate occurring in the consequent of (3.10)
also occurs in its antecedent, (3.12) must be a ﬁrst-order formula involving only �
and the relation symbol �. So, to complete the proof of the theorem it sufﬁces to

160

3 Frames

show that (3.12) is equivalent to (3.10). The implication from (3.10) to (3.12) is
simply an instantiation. To prove the other implication, assume that (3.12) and the
antecedent of (3.10) are true. That is, assume that

�

�� ��

� � � ��

���� � ����

���

� � � � � ���

���

�����

�

�

�

�

�

�

and

�

�� ��� � �����

� � � �

��

�

�

We need to show that �
above assumptions that

�� ������

� � � �

�

�

�. First of all, it follows from the

�

�� ����

���

� � � � � ���

���

�������

� � � �

��

�

�

�

�

�

�

As POS is positive, it is upwards monotone in all unary predicates occurring in
�. But, by
it, so it sufﬁces to show that �
the essential observation (3.11) in Step 2, this is precisely what the assumption

�� �� ����

���� � �

�����

� � � �

�

�

�

�

�� AT���

�

�

�

� � � �

� amounts to. �

Example 3.43 First consider the formula � �
the formula

�. Its second-order translation is

�

�� � � �

� �� ���� � � � ���

��

There are no diamonds to be pulled out here, so we can read off the minimal in-
stance ��� � � ��� � � � immediately. Instantiation gives

����

���� � � ��� � �� ���� � ��� � � ��� ��

Which (either by �-conversion or semantic reasoning) yields the following ﬁrst-
order formula.

� � � � �� ���� � � � ���

Note that this is equivalent to ���.

Our second example is the density formula �

� �

�, which has

��

�� ���

����

� � �

� � ��

����

� ��

���

�

� � �

����

�

�

�

�

�

�

�

�

�

as its second-order translation. Here we can pull out the diamond ��

:

�

�� ��

����

� � �

� ��

����

� ��

���

�

� � �

����

�

�

�

�

�

�

�

�

�

Instantiating with ��� � � ��� � � �

gives

� �� �

����

�

���

��

��

����

� �

� �

� ��

����

� ��

���

�

� �

� �

����

�

�

�

�

�

�

�

�

�

�

�

which can be simpliﬁed to ��

����

� ��

����

� ��

�

��.

�

�

�

�

�

�

3.6 Sahlqvist Formulas

161

Our last example of a very simple Sahlqvist formula is �� �

��

�� �

�. Its

�

second-order translation is

�� �� � � ��

����

� ��

���

�

� � �

�� � ��

����

� � �

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

Pulling out the diamonds ��

and ��

results in

�

�

�� ��

��

����

� ��

�

� � � � � �

� ��

����

� � �

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

���

��

Our minimal instantiation here is: ��� � � ��� �� � � � � � �
ating we obtain

��

��

�

�

�

�

�

�. After instanti-

��

��

����

� ��

�

� �� � � � � � �

� � ��

� � � �

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

��

����

� ��

� � � �

� �

�

�

�

�

�

���.

This formula simpliﬁes to ��

��

����

� ��

�

� ���� � ���

��. �

�

�

�

�

�

�

Simple Sahlqvist formulas

What is the crucial observation we need to make about the preceding proof? Sim-
ply this: the algorithm for very simple Sahlqvist formulas worked because we were
able to ﬁnd a minimal instantiation for their antecedents. We now show that min-
imal instantiations can be found for more complex Sahlqvist antecedents. First a
motivating example.

�; we will show that this
Example 3.44 Consider the formula �
formula locally corresponds to a kind of local conﬂuence (or Church-Rosser) prop-
erty of �

and �

:

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

��

��

� �

��

� ��

��

�

�

� �

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

�

�

�

�

�

�

The reason for the apparently unnatural choice of variable names will soon become
clear, as will the somewhat roundabout approach to the proof that we take. The
name ‘conﬂuence’ is explained by the following picture:

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

�

�

�

�

��

�

�

�

Let �

�

�

� ��� �

� �

� be a frame and � a state in � such that �

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

�, and let � be a state in � such that �

��. A sufﬁcient condition for a

�

�

�

162

3 Frames

valuation to make �
�. So a minimal such valuation can be deﬁned as

� true at � would be that � holds at all �

�

�

�

�

-successors of

�

��� � �� � � � �

����

�

�

That is, �

�

makes � true at precisely the �

-successors of �. As �

� �

�

�

�

� �

�

�

�, we have �

�

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

�, but what does this tell us about the (ﬁrst-

order) properties of �? The crucial observation is that by the choice of �

:

�

�

�

� �

�� �

�

�

�

�

�

�

� iff

�

�

� �

� �� ��

��

��

� ��

��

�

�

� �

�

�

����� ��

�

�

�

�

�

�

�

�

�

�

�

which yields that �

�� ��

�

��

��

� �

��

� ��

��

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

(3.13)

�����.

�

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

Conversely, assume that � has the conﬂuence property at �. In order to show that
�.
�, let � be a valuation on � such that �
-

We have to prove that �
successor � satisfying �
again; ﬁrst note that by the deﬁnition of �
Lemma 3.37 ensures that it sufﬁces to show that �
valuation �
(3.13). �

��� � � ���. Therefore,
� holds at � under the
. But this is immediate by the assumption that � is conﬂuent and

, � has an �
�. Now we use the minimal valuation �

�. By the truth deﬁnition of �

, we have �

�� and �

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

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

This example inspires the following deﬁnitions.

Deﬁnition 3.45 Let � be a modal similarity type. A boxed atom is a formula of the
are (not necessarily distinct) boxes
, . . . , �
form �
of the language. In the case where � � �, the boxed atom �
� is just the
proposition letter �. �

� (� � �), where �

� � �

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

Convention 3.46 In the sequel, it will be convenient to treat sequences of boxes
�, where
as single boxes. We will therefore denote the formula �
of indices. Analogously, we will pretend to have a
� is the sequence �
. Thus the
corresponding binary relation symbol �
�� abbreviates the formula
expression �

in the frame language �

� by �

� � � �

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

��

��

��

� ��

��

�

�

� � � � � ��

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

� �

�

�� � � ����

�

�

�

�

�

�

�

�

�

�

�

Note that this convention allows us to write the second-order translation of the
boxed atom �

�� � � ��.

� as �� ��

�

�

If � � �, � is the empty sequence �; in this case the formula �

read as � � �. Note that the Second-Order Translation of �
�� � � ��.
proposition letter �) can indeed be written as �� ��

�

�

�� should be
� (that is, of the

�

Deﬁnition 3.47 Let � be a modal similarity type. A simple Sahlqvist antecedent

3.6 Sahlqvist Formulas

163

over this similarity type is a formula built up from �, � and boxed atoms, using
only � and existential modal operators (� and �). A simple Sahlqvist formula is
an implication � � � in which � is positive (as before) and � is a simple Sahlqvist
antecedent. �

Example 3.48 Typical examples of simple Sahlqvist formulas are �

� �

�,

��

�, �

�

�

� �

�, �

�

�

�

� �

� and �

�

�

�

�

�

�

��

�

��

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

��

� �

�

�

��

�

��.

Typically forbidden in a simple Sahlqvist antecedent are:

(i) boxes over disjunctions, as in � �� � � �� � ��� � � � ��,
(ii) boxes over diamonds, as in ��
(iii) dual-triangled atoms, as in �

�,
� � �. �

� �

��

�

Theorem 3.49 Let � be a modal similarity type, and let � � � � � be a simple
Sahlqvist formula over � . Then � locally corresponds to a ﬁrst-order formula �
on frames. Moreover, �

is effectively computable from �.

���

�

�

Proof. The proof of this theorem is an adaptation of the proof of Theorem 3.42.
Consider the universally quantiﬁed second-order transcription of �:

��

� � � ��

�

��� �

�����

�

�

�

�

��

��

(3.14)

Again, we ﬁrst make sure that no two quantiﬁers bind the same variable, and that
no quantiﬁer binds �. As before, the idea of the algorithm is to rewrite (3.14) to a
formula from which we can easily read off instantiations which yield a ﬁrst-order
equivalent of (3.14).

Step 1. Pull out diamonds.
This is the same as before. This process results in a formula of the form

��

� � � ��

��

� � � ��

�REL � BOX-AT �

��

�����

(3.15)

�

�

�

�

�

cor-
where REL is a conjunction of atomic ﬁrst-order statements of the form ��
responding to occurrences of diamonds, and BOX-AT is a conjunction of (transla-
tions of) boxed atoms, that is, formulas of the form �� ��

� � � ��.

�

�

�

�

�

�

Step 2. Read off instances.
Let � be a unary predicate occurring in (3.15), and let �
� be
all the (translations of the) boxed atoms in the antecedent of (3.10) in which the
predicate � occurs. Observe that every �
� � � ��,
where �

is a sequence of diamond indices (recall Convention 3.46). Deﬁne

is of the form �� ��

�, . . . , �

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

��� � � ��� ��

�

� � � � � � �

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

Again, ���
BOX-AT true.

�

�, . . . , ���

� form the minimal instances making the antecedent ����

�

164

3 Frames

The remainder of the proof is the same as the proof of Theorem 3.42, with the

proviso that all occurrences of ‘AT’ should be replaced by ‘BOX-AT’. �

As in the case of very simple Sahlqvist formulas, the algorithm is best understood
by inspecting some examples:

Example 3.50 Let us investigate some of the formulas given in Example 3.48. The
� has the following second-order transla-
simple Sahlqvist formula �
tion:

� �

�

�

�

�

�

�� ��� ��

�� � � ��

� �� ��

�� � � � ���

��

�

BOX-AT

There are no diamonds to be pulled out here, so we can read off the required sub-
�� immediately. Carrying out the substitution
stitution instance ��� � � ��� �
we obtain

��

��

�

�

�� ��

�� � �

��� � �� ��

�� � �

�� ��

��

��

�

��

which is equivalent to �� ��

�� � �

�� �.

�

��

Next we consider the conﬂuence formula �

�

�

�

� �

�, whose second-

�

�

�

�

order translation is

�� ���

��

��

� �� ��

�

� � � ��� � ��

��

��

� ��

��

�

�

� � �

����

�

�

�

�

�

�

�

�

�

�

�

�

�

Pulling out the existential quantiﬁcation ��

yields

�

�� ��

��

��

� �� ��

�

� � � ��

� ��

��

��

� ��

��

�

�

� � �

����

�

�

�

�

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

BOX-AT

The minimal instance making BOX-AT true is ��� � � ��� �
ating we obtain

� �� �

��

�

�

�

�. After instanti-

�

�

��

��

��

� �� ��

�

� � �

�

�� � ��

��

��

� ��

��

�

�

� �

�

�

����

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

which can be simpliﬁed to

��

��

��

��

� �

��

� ��

��

�

�

� �

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

�

�

�

�

�

�

As our ﬁnal example, let us treat a formula using a dyadic modality �:

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

� �

�� �

��

���

�

�

�

�

�

�

We use a ternary relation symbol � for the triangle �. Its second-order translation
is the rather formidable looking

�� �� ���

�

�� ��

�

� �� ��

�

� � � �� �

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

� � �

� � �� ��

�

� � ����

�

�

�

�

�

��

�

� �� ��

�� � ��

�

�� ��

�

� ��

� � �

����

�

�

�

�

�

�

�

from which we can pull out the diamonds ��

, ��

and ��

. This leads to

�

�

�

3.6 Sahlqvist Formulas

165

���

�� ����

�

��

�

� ��

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

���

��

�

�� ��

�

� � � �� � � �

� �� ��

�

� � ��� �

��

�

�

��

�

�� ��

�� � ��

�

�� ��

�

� ��

� � �

����

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

Now we can easily read off the required instantiations:

��� � � ��� ��

�

� � � � �

�

��

�

�

���� � ��� ��

�

���

��

�

Performing the substitution ���� ��� � ������� and deleting the tautological parts
from the antecedent gives

��

�

��

�� ��

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

�� ��

�� � ��

�

�� ��

�

� �

�

�

� ��

�

�

� �

� �

���� �

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

Sahlqvist formulas

We are now ready to introduce the full Sahlqvist fragment and the full version of
the Sahlqvist-van Benthem algorithm.

Deﬁnition 3.51 Let � be a modal similarity type. A Sahlqvist antecedent over � is
a formula built up from �, �, boxed atoms, and negative formulas, using �, � and
existential modal operators (� and �). A Sahlqvist implication is an implication
� � � in which � is positive and � is a Sahlqvist antecedent.

A Sahlqvist formula is a formula that is built up from Sahlqvist implications by
freely applying boxes and conjunctions, and by applying disjunctions only between
formulas that do not share any proposition letters. �

Example 3.52 Both simple and very simple Sahlqvist formulas are examples of
Sahlqvist formulas, as are �

�, and �

��, � �

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

�� �

��. As with simple Sahlqvist formulas, typically forbidden
combinations in Sahlqvist antecedent are ‘boxes over disjunctions,’ ‘boxes over di-
amonds,’ and ‘dual-triangled atoms’ as in �

� � � (see Example 3.48). �

�� �

�

�

�

�

The following lemma is instrumental in reducing the correspondence problem for
arbitrary Sahlqvist formulas, ﬁrst to that of Sahlqvist implications, and then to to
that of simple Sahlqvist formulas.

Lemma 3.53 Let � be a modal similarity type, and let � and � be � -formulas.

166

3 Frames

(i) If � and ���� are local correspondents, then so are �

� and �� ��

�

�

�� �

�������.

(ii) If � (locally) corresponds to �, and � (locally) corresponds to �, then � � �

(locally) corresponds to � � �.

(iii) If � locally corresponds to �, � locally corresponds to �, and � and � have
no proposition letters in common, then � � � locally corresponds to � � �.

Proof. Left as Exercise 3.6.3. �

The local perspective in part one and three of the Lemma is essential. For instance,
one can ﬁnd a modal formula � that globally corresponds to a ﬁrst-order condition
�� ���� without �
� globally corresponding to the formula ���� ���� � �����;
see Exercise 3.6.3.

Theorem 3.54 Let � be a modal similarity type, and let � be a Sahlqvist formula
over � . Then � locally corresponds to a ﬁrst-order formula �
��� on frames. More-
over, �

is effectively computable from �.

�

�

Proof. The proof of the theorem is virtually the same as the proof of Theorem 3.49,
with the exception of the use of Lemma 3.53 and of the fact that we have to do some
pre-processing of the formula �.

By Lemma 3.53 it sufﬁces to show that the theorem holds for all Sahlqvist im-
plications. So assume that � has the form � � � where � is a Sahlqvist antecedent
and � a positive formula. Proceed as follows.

Step 1. Pull out diamonds and pre-process.
Using the same strategy as in the proof of Theorem 3.49 together with equivalences
of the form

��� � � � � � � � � �� � � � � �� � � � �

and

� � � � �� � � � � � � � � � � � � � � � � ��

we can rewrite the second-order translation of � � � into a conjunction of formu-
las of the form

��

� � � ��

��

� � � ��

�

�

�

�

�REL � BOX-AT � NEG �

��

�

�����

(3.16)

�� cor-
where REL is a conjunction of atomic ﬁrst-order statements of the form �
responding to occurrences of diamonds and triangles, BOX-AT is a conjunction of
(translations of) boxed atoms, and NEG is a conjunction of (translations of) neg-
ative formulas. By Lemma 3.53(ii) it sufﬁces to show that each formula of the
form displayed in (3.16) has a ﬁrst-order equivalent. This is done by using the
equivalence

�

�� � NEG � � � � �� � � � �NEG��

3.6 Sahlqvist Formulas

167

where ���� is the positive formula that arises by negating the negative formula
NEG. Using this equivalence we can rewrite (3.16) to obtain a formula of the form

��

� � � ��

��

� � � ��

�

�

�

�

�REL � BOX-AT � POS��

and from here on we can proceed as in Step 2 of the proof of Theorem 3.49. �

Example 3.55 By way of example we determine the local ﬁrst-order correspon-
dents of two of the modal formulas given in Example 3.52. To determine the
ﬁrst-order correspondent of the Sahlqvist formula �
�� we ﬁrst recall that
� is ���. So, by Lemma 3.53(i)
the local ﬁrst-order correspondent of � �

�� �

�

�

�

�� �

�� locally corresponds to �� ���� � ����.

�

Next we consider the Sahlqvist formula �� �

�

�

��� �

�. Its translation is

�� �� � � �� ���� � �� �� � �� ���� � � � ���

Pulling out the diamond produces

�� �� � � �

� ���

� �� �

� �� ���� � � � ��

�

BOX-AT

���

���

and moving the negative part �� � to the consequent we get

����

����

� �� �

�

��

�

�� �� � � �

� ���

� � � � �� ���� � � � �

��

BOX-AT

REL

POS

The minimal instantiation to make � � true is ��� � � �. After instantiation we
obtain

����

����

��

�

�

�� ���� � � � � � �� ���� � � � ����

which can be simpliﬁed to �� ���� � � �� � � ����. �

Exercises for Section 3.6
3.6.1 Compute the ﬁrst-order formulas locally corresponding to the following Sahlqvist
formulas:

�

(a) �
(b) �
(c) �
(d) �
(e) �
(f) �

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

�

��

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

�

�

�

�

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

��

�

�

�

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

�,

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

��.

��

�, for arbitrary natural numbers �, �, � and �,
�,

3.6.2

(a) Show that the formula �

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

� does not locally correspond

to a ﬁrst-order formula on frames. (Hint: modify the frame of Example 3.11.)
(b) Use this example to show that dual-triangled atoms cannot be allowed in Sahlqvist

antecedents.

168

3 Frames

3.6.3 Prove Lemma 3.53:

(a) Show that if � and �
(b) Prove that if � (locally) corresponds to �

� locally correspond, so do �

�

�

�

then �

�

� (locally) corresponds to �

�

� �

�

�

�

�

�.

� and �

�

�

��

�

�

�

�

�

��.

�, and � (locally) corresponds to �

�

�,

�

�

�

�

(c) Show that if � locally corresponds to �, � locally corresponds to �

�, and �
� locally corresponds to

�

�

and � have no proposition letters in common, then �

�

�

�

�

�

�

� �

�

�.

(d) Prove that (a) and (c) do not hold for global correspondence, and that the condition
on the proposition letters in (c) is necessary as well. (Hint: for (a), think of the
modal formula ��

� and the ﬁrst-order formula �

���

���

���

�

�

�

�

�

�

�.)

���

3.7 More about Sahlqvist Formulas

It is time to step back and think more systematically about the Sahlqvist fragment,
for a number of questions need addressing. For a start, does this fragment con-
tain all modal formulas with ﬁrst-order correspondents? And why did we forbid
disjunctions in the scope of boxes, and occurrences of nested duals of triangles
in Sahlqvist antecedents, while we allowed boxed atoms? Most interesting of all,
which ﬁrst-order conditions are expressible by means of Sahlqvist formulas? That
is, is it possible to prove some sort of converse to the Sahlqvist Correspondence
Theorem?

Limitative results

To set the stage for our discussion, we ﬁrst state (without proof) the principal limi-
tative result in this area: Chagrova’s Theorem. Good presentations of the proof are
available in the literature; see the Notes for references.

Theorem 3.56 (Chagrova’s Theorem) It is undecidable whether an arbitrary ba-
sic modal formula has a ﬁrst-order correspondent.

This implies that, even for the basic modal language, it is not possible to write
a computer program which when presented with an arbitrary modal formula as
input, will terminate after ﬁnitely many steps, returning the required ﬁrst-order
correspondent (if there is one) or saying ‘No!’ (if there isn’t).

Quite apart from its intrinsic interest, this result immediately tells us that the
Sahlqvist fragment cannot possibly contain all modal formulas with ﬁrst-order cor-
respondents. For it is straightforward to decide whether a modal formula is a Sahl-
qvist formula, and to compute the ﬁrst-order correspondents of Sahlqvist formulas.
Hence if all modal formulas with ﬁrst-order correspondents were Sahlqvist, this
would contradict Chagrova’s Theorem.

3.7 More about Sahlqvist Formulas

169

But a further question immediately presents itself: is every modal formula with
a ﬁrst-order correspondent equivalent to a Sahlqvist formula? (The preceding ar-
gument does not rule this out.) The answer is no: there are modal formulas corre-
sponding to ﬁrst-order frame conditions which are not equivalent to any Sahlqvist
formula.

Example 3.57 Consider the conjunction of the following two formulas:

(M)
(4)

�

�

�

�

� �

�

��

�

� �

�.

(M) is the McKinsey formula we discussed in Example 3.11, and (4) is the transitiv-
ity axiom. It is obvious that M itself is not a Sahlqvist axiom, and by Example 3.11
it does not express a ﬁrst-order condition.

It requires a little argument to show that the conjunction � � � is not equivalent
to a Sahlqvist formula. One way to do so is by proving that � � � does not have a
local ﬁrst-order correspondent (cf. Exercise 3.7.1).

Nevertheless, the conjunction � � � does have a ﬁrst-order correspondent, as we

can prove the following equivalence for all transitive frames �:

�

�

� iff �

�� ���� ���� � �� ���� � � � ����

(3.17)

We leave the right to left direction as an exercise to the reader. To prove the other
direction, we reason by contraposition. That is, we assume that there is a transitive
� ��� �� on which the McKinsey formula is valid, but which does not
frame �
satisfy the ﬁrst-order formula given in (3.17). Let � be a state witnessing that the
ﬁrst-order formula in (3.17) does not hold in �. That is, assume that each successor
� of � has a successor distinct from it. We may assume that the frame is generated
from �, so that �

�� ���� ���� � � �� � �.

In order to derive a contradiction from this, we need to introduce some terminol-
ogy. Call a subset � of � coﬁnal in � if for all � � � there is an � � � such
that ���. We now claim that

� has a subset � such that both � and � � � are coﬁnal in � �

(3.18)

From (3.18) we can immediately derive a contradiction by considering the valua-
tion � given by � ��� � �. For, coﬁnality of � implies that �
�,
while coﬁnality of � � � likewise gives �
�.

��. But then �

� � �� � �

� � �� �

� � �� �

��

��

�

�

�

�

�

�

To prove (3.18), consider the collection � of all pairs of disjoint subsets � ,
� � � satisfying �� � � �� � � ��� and �� � � �� � � ���. This set is non-
�� ���� ���� � � �� � �; order it under coordinate-wise inclusion.
empty because �
It is obvious that every chain in this partial ordering is bounded above; hence, we

170

3 Frames

may apply Zorn’s Lemma and obtain a maximal such pair � , �. We claim that

Since � and � are disjoint, this implies that � � � � � and thus proves (3.18).

� � � � �

(3.19)

Suppose that (3.19) does not hold. Then there is an element � � � which
belongs neither to � nor to �.
If there were some � � � with ��� then the
pair �� � ���� � � would belong to �, contradicting the maximality of �� � � �.
Likewise, there is no � � � with ���. Even so, we will deﬁne non-empty sets
� � �, again contradicting the maximality of
and
�� � � �. Then choose an element
�. Continue this process
will belong to � � �; this is by transitivity of

� such that �� � �
�� � � �. First put � in �
in �
and put �
of � such that ��

�. Now choose an element �
� — remember that �

of � such that ���

and put �

into �

and �

� � � �

� �� �

�� �

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

and observe that none of the �
� and our assumption on �.

�

� �

The process will ﬁnish if, for instance, some � has just been put in �

its successors have already been put in �
we break off the process; at this moment it is obvious that each � � � � �
a successor in � � �
in � � �
in the sequence ���
it must belong to �
means that we could put a successor �
other case in which the process may ﬁnish is symmetric to the case described.

�, but all of
� at some earlier state. In such a case
� has
� distinct from � has a successor
�, let � be the ﬁrst element
�,
�; but since we did not break off the process at this stage, this
. The only

� � � such that ���. If � itself does not belong to �

�. To show that � itself has a successor in �

�, and that each � � � � �

�; by transitivity, ���

of � in �

��

��

�

�

�

�

�

Finally, if the process does not ﬁnish in this way we are dealing with an inﬁnite
� belongs to �. �

� � �. But then the pair �� � �

sequence ���

� � � �

��

��

�

�

�

�

�

the formula �

Obviously, the example begs the question whether there is a modal formula that
locally corresponds to a ﬁrst-order formula without being equivalent to a Sahlqvist
� � � is a
formula. The answer to this question is afﬁrmative:
counterexample. In Exercise 3.7.1 the reader is asked to show that it has a local
ﬁrst-order correspondent; in Chapter 5 we will develop the techniques needed to
prove that the formula is not equivalent to a Sahlqvist formula, see Exercise 5.6.2.
Thus the Sahlqvist fragment does not contain all modal formulas with ﬁrst-order
correspondents. So the next question is: can the Sahlqvist fragment be further
extended? The answer is yes — but we should reﬂect a little on what we hope
to achieve through such extensions. The Sahlqvist fragment is essentially a good
compromise between the demands of generality and simplicity. By adding further
restrictions it is possible to extend it further, but it is not obvious that the resulting
loss of simplicity is really worth it. Moreover, the Sahlqvist fragment also gives
rise to a matching completeness theorem; we would like proposed extensions to
do so as well. We don’t know of simple generalizations of the Sahlqvist fragment

3.7 More about Sahlqvist Formulas

171

which manage to do this. In short, while there is certainly room for experiment
here, it is unclear whether anything interesting is likely to emerge.

However, one point is worth stressing once more: the Sahlqvist fragment cannot
be further extended simply by dropping some of the restrictions in the deﬁnition
of a Sahlqvist formula. We forbid disjunctions in the scope of boxes and nested
duals of triangles in Sahlqvist antecedents for a very good reason: these forbidden
combinations easily lead to modal formulas that have no ﬁrst-order correspondent,
as we have seen in Example 3.11 and Exercise 3.6.2.

Kracht’s theorem

Let’s turn to a nice positive result. As has already been mentioned, not only does
each Sahlqvist formula deﬁne a ﬁrst-order class of frames, but when we use one
as an axiom in a normal modal logic, that logic is guaranteed to be complete with
respect to the elementary class of frames the axiom deﬁnes. (This is the content of
the Sahlqvist Completeness Theorem; see Theorem 4.42 for a precise statement.)
So it would be very pleasant to know which ﬁrst-order conditions are the corre-
spondents of Sahlqvist formulas. Kracht’s Theorem is a sort of converse to the
Sahlqvist Correspondence Theorem which gives us this information.

�

Before we can deﬁne the fragment of ﬁrst-order logic corresponding to Sahl-
qvist formulas we need some auxiliary deﬁnitions; we also introduce some helpful
notation. For reasons of notational simplicity, we work in the basic modal similar-
ity type. First of all, we will abbreviate the ﬁrst-order formula �� ���� � �����
������, speaking of restricted quantiﬁcation and calling � the restrictor
to ���
������. We will call the
of �. Likewise �� ���� � ����� is abbreviated to ���
�� restricted quantiﬁers. If we wish not to specify
constructs ���
�. Moreover, if we
the restrictor of a restricted quantiﬁer we will write �
don’t wish to specify whether a quantiﬁer is existential or universal we denote it
� in the restricted case). Second, for the duration of this subsection it will
by � (�
be convenient for us to consider formulas of the form � �� � as atomic. Third, in
this subsection we will work exclusively with formulas in which no variable occurs
both free and bound, and in which no two distinct (occurrences of) quantiﬁers bind
the same variable; we will call such formulas clean.

�� and ���

� or �

�

�

�

�

�

Now we call a formula restrictedly positive if it is built up from atomic formu-
las, using �, � and restricted quantiﬁers only; observe that monadic predicates oc-
cur positively in restrictedly positive formulas. Finally, we assume that the reader
knows how to rewrite an arbitrary positive propositional formula to a disjunctive
normal form or DNF (that is, to an equivalent disjunction of conjunctions of atomic
formulas) and to a conjunctive normal form or CNF (that is, to an equivalent con-
junction of disjunctions of atomic formulas).

172

3 Frames

The crucial notion in this subsection is that of a variable occurring inherently

universally in a ﬁrst-order formula.

Deﬁnition 3.58 We say that an occurrence of the variable � in the (clean!) formula
� is inherently universal if either � is free, or else � is bound by a restricted quan-
��� which is not in the scope of an existential quantiﬁer.
tiﬁer of the form ���
A formula ���� in the basic ﬁrst-order frame language is called a Kracht formula
if � is clean, restrictedly positive and furthermore, every atomic formula is either
of the form � � � or � �� �, or else it contains at least one inherently universal
variable. �

�

Restricted quantiﬁcation is obviously the modal face of quantiﬁcation in ﬁrst-order
logic; indeed, we could have deﬁned the standard translation of a modal formula
using this notion. As for Kracht formulas, ﬁrst observe that every universal re-
stricted ﬁrst-order formula satisﬁes the deﬁnition. A second example of a Kracht
formula is ���
�����: note that it does not matter that the ‘�’
in ��� falls within the scope of an existential quantiﬁer; what matters is that the
universal quantiﬁer that binds � does not occur within the scope of any existen-
��� � � is not
tial quantiﬁcation. On the other hand, the formula ���
a Kracht formula since the occurrence of neither � nor � in � � � is inherently
universal: � is disqualiﬁed because it is bound by an existential quantiﬁer and �
because it is bound within the scope of the existential quantiﬁer ���

��.

�����

�����

�����

�

�

�

�

�

�

The following result states that Kracht formulas are the ﬁrst-order counterparts
of Sahlqvist formulas — but not only that. As will become apparent from its proof,
from a given Kracht formula we can compute a Sahlqvist formula locally corre-
sponding to it. The reader is advised to glance at the examples provided below
while reading the proof.

Theorem 3.59 Any Sahlqvist formula locally corresponds to a Kracht formula;
and conversely, every Kracht formula is a local ﬁrst-order correspondent of some
Sahlqvist formula which can be effectively obtained from the Kracht formula.

Proof. For the left to right direction, we leave it as an exercise to the reader to
show that the algorithm discussed in the sections 3.5 and 3.6 in fact produces,
given a Sahlqvist formula, a ﬁrst-order correspondent within the Kracht fragment.
We’ll give the proof of the other direction: we’ll show how rewrite a given Kracht
formula to an equivalent Sahlqvist formula.

Our ﬁrst step is to provide special prenex formulas as normal forms for Kracht

formulas. Deﬁne a type 1 formula to be of the form

�

�

�

�

�

�

� � � �

�

�

� � �

�

� ��

� � � � � �

� �

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

such that �, � � � and each variable is restricted by an earlier variable (that is, the

3.7 More about Sahlqvist Formulas

173

�

�

�

�

�

�

is some �

restrictor of any �
or some �

is either some
with � � � and the restrictor of any �
with � � �. Furthermore we require that � is a DNF of formulas
� � �, � �� �, ���, � � � and ��� (that is, we allow all atomic formulas that are
not of the form ���
�). Here and in the remainder of this proof we use
the convention that � and � denote arbitrary variables in ��
and � an arbitrary variable in ��

�.
Clearly then, type 1 formulas form a special class of Kracht formulas. This
inclusion is not proper (modulo equivalence), since we can prove the following
claim.

� or � � �

, �

� � � � � �

� � � � � �

� � � � � �

�

�

�

�

�

�

�

Claim 1 Every Kracht formula can be effectively rewritten into an equivalent type
1 formula.

Proof of Claim. Let ���
atomic formulas using �, � and restricted quantiﬁers. Furthermore, since ���
clean, in a subformula of the form �
�. Hence, we may use the equivalences

� be a Kracht formula. By deﬁnition it is built up from
� is
� � the variable � may not occur outside of

�

�

�

�

�

�

�

�

� � � � � �

� �� � � �

(3.20)

(where � uniformly denotes either � or �) to pull out quantiﬁers to the front.
However, if we want to remain within the Kracht fragment we have to take care
about the order in which we pull out quantiﬁers.

�

�

�

Without loss of generality we may assume that each inherently universal variable
for some
for some �, while each of the remaining variables is named �
� or � � �
� is of the form ���

is named �
�. This ensures that no atomic subformula of ���
(with distinct variables � and �

�).
Observe also that in every subformula of the form ����

��� ���, the variable
then it is a bound variable of �; hence,
� occurs free. If this � is not the variable �
�. This
the mentioned subformula must occur in the scope of a quantiﬁer �
quantiﬁcation must have been universal, for otherwise, the variable � could not
have been among the inherently universal ones. But this means that the variable
. This shows that
� itself must be inherently universal as well, so � is some �
� we end up with a
by successively pulling out restricted universal quantiﬁers �
Kracht formula of the form

�

�

�

�

�

�

�

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

��

� � � � � �

� �

� � � � � �

��

�

�

�

�

�

�

such that each atomic formula of �
contains some occurrence of a variable �
some �

with � � �.

� is of the form � � � or � �� �, or else it
is
. Furthermore, the restrictor of each �

�

�

�

It remains to pull out the other restricted quantiﬁers from �

�. But this can easily
be done using the equivalences of (3.20), since we do not have to worry anymore

174

3 Frames

about the order in which we pull out the quantiﬁers. In the end, we arrive at a
formula of the form

�

�

�

�

��

�

�

� � � �

�

�

� � �

�

�

��

� � � � � �

� �

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

such that the atomic subformulas of �
(in fact, they are the very same formulas), while in addition, �
Hence, if we rewrite �

�� satisfy the same condition of those in �
�� is quantiﬁer free.

�� into disjunctive normal form, we are ﬁnished.

�

�

Enter diamonds and boxes. A type 2 formula is a formula in the second-order frame
language of the form

�

�

�

�

��

�

�

��

� � �

��

��

� � �

��

�

�

� � � �

�

��

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

such that each �
of formulas ��

�

is a conjunction of boxed atoms in �
���, with � some modal formula which is positive in each �

, whereas � is a DNF
.

and �

, �

�

�

�

�

�

�

�

Claim 2 Every type 1 formula can be can be effectively rewritten into an equiva-
lent type 2 formula.

Proof of Claim. Now the prominent role of the inherently universal formulas will
come out: they determine the propositional variables of the Sahlqvist formula and
the ‘BOX-AT’ part of its antecedent. Consider the type 1 formula

�

�

�

�

�

�

� � � �

�

�

� � �

�

� ��

� � � � � �

� �

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

� � � �

� � �

by �

We abbreviate the sequence �
��, and use similar abbreviations for
other sequences of quantiﬁers. Recall that � is a DNF of formulas � � �, � �� �,
and ��
, ���
�. Our ﬁrst move is to replace such subformulas with the
���, ��
���, ��
�, respectively; call
� and ��
formulas ��
�.
the resulting formula �
Our ﬁrst claim is that

�, ��

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

�

�� � is equivalent to

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

��

�

�

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

(3.21)

�

�

�

�

�

�

�

Forbidding as (3.21) may look, its proof is completely analogous to proofs in Sec-
tions 3.5 and 3.6: the direction from right to left is immediate by instantiation,
� is monotone in each
while the other direction simply follows from the fact that �
predicate symbol �

and �

.

�

�

�

Two remarks are in order here. First, since � may contain atomic formulas of the
(that is, with both variables being inherently universal),

and �

form ��

� �

�

�

�

�

�

3.7 More about Sahlqvist Formulas

175

�

�

�

�

�

�

�

� or with ��

there is some choice here. For instance, the formula ��
may be replaced with
�. Having this choice can sometimes be of use if
either ��
one wants to ﬁnd Sahlqvist correspondents satisfying some additional constraints.
Related to this is our second remark: we don’t need to introduce both proposi-
tional variables �
. We can do with any supply of variables that is
sufﬁcient to replace all atomic formulas of � with the standard translation of either
�. A glance at the examples below will make this

for each �

� or ��

�, ��

and �

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

point clear.

We are now halfway through the proof of Claim 2: observe that �

��� with � positive in each �

� is already a
. It remains to eliminate
��. This will be done step by step, using the following

� �

�

�

�

DNF of formulas ��
the quantiﬁer sequence �
procedure.

�

Consider the formula

���

� �

��

�

�

�

��

�

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

�

�

�

�

(3.22)

where each modal formula �
a �
the existential quantiﬁer over the disjunction, yielding a disjunction of formulas

; � is either an � or
with � � � � �. We ﬁrst distribute

with � � �; and each � is either an � or a �

is positive in all variables �

, �

�

�

��

�

�

�

�

���

� �

��

��

�

��

�

��

��

�

��

�

�

�

�

�

(3.23)

We may assume all these variables � to be distinct (otherwise, replace ��

�

�

��

� �

��

� with ��
does not occur among the �’s, add a conjunct ��

�); we may also assume that �

� �

��

�

��

�

�

��

is the variable �
���). But then (3.23)

��

�

�

��

�

��

�

��

(if �
is equivalent to the formula

��

�

��

�

��

�

��

�

��

�

�

� �

��

��

��

���

�

�

whence (3.22) is equivalent to a disjunction of such formulas. Observe further that

does not occur in these formulas.

�

�

��

�

This shows how to get rid of an existential innermost restricted quantiﬁer of the
��. A universal innermost restricted quantiﬁer can be removed dually, by
prenex �
� into a conjunctive normal form; details are left to the
ﬁrst converting the matrix �
reader. In any case, it will be clear that by this procedure we can rewrite any type
1 formula into an equivalent type 2 formula.

�

We are now almost through with the proof of Theorem 3.59. All we have to do
now is show how to massage arbitrary type 2 formulas into Sahlqvist shape.

Claim 3 Any type 2 formula can be can be effectively rewritten into an equivalent
Sahlqvist formula.

176

3 Frames

Proof of Claim. Let

�

�

�

��

�

�

�

� �

��

��

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

(3.24)

be an arbitrary type 2 formula.

�

�

First we rewrite � into conjunctive normal form, and we distribute the implica-
tion and the prenex of universal quantiﬁers over the conjunctions. Thus we obtain
a conjunction of formulas of the form

�

�

�

��

�

�

�

�

��

��

��

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

(3.25)

� is a disjunction of formulas of the form ��
. As before, we may assume that each �

��� with each � positive in
occurs in exactly one disjunct

�

�

�

and �

�

�

�, so (3.25) is equivalent to a formula

where �
all �
of �

�

�

�

�

��

��

�

�

�

� �

��

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

�

�

�

�

�

�

�

�

where each �
(3.25) is equivalent to the formula

�

�

is a Sahlqvist antecedent and each �

is positive. But clearly then,

�

�

�

�

�

��

�

�

�

���

��

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

�

Observe that each modal formula �

� ��

is a Sahlqvist antecedent.

�

�

But now, as before, working inside out we may eliminate all remaining restricted

quantiﬁers, step by step. For, observe that the formula

�

�

�

�

� � � �

�

���

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

��

�

�

�

�

�

�

is equivalent to

�

�

�

�

� � � �

�

��

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

��

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

�����

�

�

Note that �

�

�

�

�

is a Sahlqvist antecedent if �

and �

are.

�

�

�

��

�

�

��

It turns out that for some Sahlqvist antecedent �, (3.25) is equivalent to the

second-order formula

�

�

�

��

�

�

� �

����

�

�

�
3.7 More about Sahlqvist Formulas

177

But then (3.24) is equivalent to a conjunction of such formulas, and thus equivalent
to a formula

�

�

�

��

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

which is the local second-order frame correspondent of the formula
which is obviously in Sahlqvist form.

�

� �,

�

�

�

This completes the proof of the third claim, and hence of the theorem. �

�

Example 3.60 Consider the formula

���

� � ���

�

����

�

����

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

This is already a type 2 Kracht formula, so we proceed by the procedure described
in the proof of Claim 2 in the proof of Theorem 3.59. According to (3.21), ���
is equivalent to the second order formula

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

���

�

� �

�

�

� � ���

�

����

�

�

��

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

Then, using the equivalences described further on in the proof of Claim 2 we obtain
the following sequences of formulas that are equivalent to ���

�:

�

�

�

�

�

�

��

��

��

���

�

� �

�

�

� � ���

�

����

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

��

���

�

� �

�

�

� � ���

�

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

��

���

�

� �

�

�

� �

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

�

�

�

�

�

��

��

��

The last formula is a type 2 formula. Hence, the only thing left to do is to rewrite
it to an equivalent Sahlqvist formula; this we do via the sequence of equivalent
formulas below, following the pattern of the proof of Claim 3.

�

�

�

��

��

��

��

� ���

�

� �

�

�

� �

�

�

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

��

� ���

�

� ��

�

�

� � �

�

�

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

��

��

��

�

��

� ���

�

� ��

�

�

� �

��

�

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

��

��

��

�

��

� ����

�

� �

�

�

� �

��

�

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

��

��

��

�

��

� �����

�

�

�

�

� �

��

�

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

��

��

��

�

��

� ��

�

�

� �

��

�

�� �

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

��

� �

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

��

��

��

�

��

�

��

�

� �

�

� � �� ��

�

�

�

�

�

�

��

��

��

This means that ���

� locally corresponds to the Sahlqvist formula �

�

��

�

�

�

��

�

�

� � �, or to the equivalent formula ��

�

�

�

��

. �

�

�

�

178

3 Frames

Example 3.61 Consider the Kracht formula

���

� � ���

�

����

�

� ���

�

� ��

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

�

�

�

According to (3.21), ���

� is equivalent to

�

�

�

�

�

�

��

��

��

���

�

����

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

�

�

�

�

�

� �

��

� �

�

�

� �

��

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

��

��

��

�

and to

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

���

�

����

�

� �

��

�

�

� �

��

�

�

� �

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

The latter is a type 2 formula; in order to ﬁnd a Sahlqvist equivalent for it, we
proceed as follows:

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

���

�

����

�

� �

��

�

�

� �

��

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

���

�

����

�

� ��

��

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

��

�

��

��

���

�

����

�

� ��

��

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

��

��

�

�

��

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

��

��

����

�

����

�

� �

��

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

��

��

�

�

�

�

�

�

����

�

�

� �

���

��

�

�

�

�

�

�

����

�

�

� �

���

�

��

��

����

�

� �

��

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

���

�

�

����

�

�

� �

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

��

�

��

��

����

�

� �

��

�

�

� �

�

���

�

�

� �

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

�

�

�

��

��

�

��

��

�����

�

�

��

�

�

� �

�

���

�

�

� �

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

�

�

�

��

��

�

��

��

��

�

��

�

�

�� �

�

���

�

�

� �

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

��

��

�

�

�

�

�

��

��

��

�

��

�

�

� �

���

�

�

� �

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

��

�

�

�

�

From this, the fastest way to proceed is by observing that the last formula is equiv-
alent to

�

�

��

�

�

�

�

��

��

�

�

��

�

�

� � �

���

�

�

� �

����

�

�

�

�

�

�

�

�

�

and hence, to the Sahlqvist formula

�

�

�

�

��

�

�

� �

��

�

�

� �

�� �

�

�

�

�

�

Example 3.62 Consider the type 1 Kracht formula

���

� � ���

�

����

�

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

According to (3.21), we can rewrite ���

� into the equivalent

�

�

�

�

��

��

��

���

�

� �

��

� � ���

�

�

����

�

�

�

�

�

�

�

�

�

�

3.7 More about Sahlqvist Formulas

179

and, hence, to

�

�

�

��

��

��

���

�

� �

��

� �

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

This is a type 2 formula for which we can ﬁnd a Sahlqvist equivalent as follows:

�

�

�

��

��

��

���

�

� �

��

� �

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

��

���

�

� ��

��

� � �

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

��

��

�

��

����

�

� �

��

� �

��

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

��

��

�

��

� �

��

� � ���

�

�

��

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

��

��

�

�

�

��

� �

��

� �

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

��

�

�

�

��

�

����

�

�

���

�

�

�

�

�

��

�

�

The latter formula is equivalent to the Sahlqvist formula �
the latter formula is equivalent to ��
always provide the simplest correspondents!) �

� and, hence, to �

�. (Obviously,
�. Our algorithm will not

��

�

�

This ﬁnishes our discussion of Sahlqvist correspondence. In the next chapter we
will see that Sahlqvist formulas also have very nice completeness properties, in
that any modal logic axiomatized by Sahlqvist formulas is complete with respect
to the class of frames deﬁned by (the global ﬁrst-order correspondents of) the for-
mulas. Here Kracht’s theorem can be useful: if we want to axiomatize a class of
frames deﬁned by formulas of the form �� ���� with ���� a Kracht formula, then
it sufﬁces to compute the Sahlqvist correspondents of these formulas and add these
as axioms to the basic modal logic.

Exercises for Section 3.7
3.7.1

(a) Prove that the conjunction � � � of McKinsey’s formula ��

� and
� does not have a local ﬁrst-order correspondent.

��

�

�

the transitivity formula �
Conclude that this conjunction is not equivalent to a Sahlqvist formula.

��

�

�

(b) Show that on the other hand, the formula �

�

� � does have a local ﬁrst-order

correspondent.

3.7.2 Prove that the local correspondent of a Sahlqvist formula is a Kracht formula.

3.7.3 Find Sahlqvist formulas that locally correspond to the following formulas:

(a) ��
(b) ��
(c) ��
(d) ��

���,

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

�

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

���

��

�

��

�

���

� �

�

� �

�

� �

�

���.

�

�

�

�

�

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

��

�

���

��

�

3.7.4 Prove that if �
a simple Sahlqvist formula.

�

� is a simple Sahlqvist formula, then �

�

�

�

�

� is equivalent to

180

3 Frames

3.7.5 Let � be the basic temporal similarity type. Show that over the class of bidirectional
frames, every simple Sahlqvist formula is equivalent to a very simple Sahlqvist formula.
(Hint: ﬁrst ﬁnd a very simple Sahlqvist formula that is equivalent to the formula � ��
�� �.)

�

3.8 Advanced Frame Theory

The main aim of this section is to prove Theorem 3.19, the Goldblatt-Thomason,
characterizing the elementary frame classes that are modally deﬁnable. We’ll also
prove a rather technical result needed in our later work on algebras. We’ll start by
proving the Goldblatt-Thomason Theorem.

Theorem 3.19 Let � be a modal similarity type. A ﬁrst-order deﬁnable class � of � -
frames is modally deﬁnable if and only if it is closed under taking bounded morphic
images, generated subframes, disjoint unions and reﬂects ultraﬁlter extensions.

Proof. The preservation direction follows from earlier results. For the other di-
rection let � be a class of frames which is elementary (hence, closed under taking
ultraproducts), closed under taking bounded morphic images, generated subframes
� be the logic of �;
and disjoint unions, and reﬂecting ultraﬁlter extensions. Let �
� deﬁnes �. In order
that is, �
to avoid cumbersome notation we restrict ourselves to the basic modal similarity
type.

�. We will show that �

�, for all �

� �� �

�

�

�

�

�

Let �

� ��� �� be a frame such that �

�. We need to show that � is a
member of �. This we will do by moving around lots of structures; here’s a map
of where we are heading for in the proof:

�

�

�

�� �

�

� � � � �

�

�

�

�

� � �

��

�

� ��

1

6

�

�

5

�

�

�

�

�

4

3

�

�

�

�

�

2

�

�

�

�

�

�

�

�

�

First, we can assume without loss of generality that � is point-generated. For if
� validates �
�, then each of its point-generated does so as well. And if we can
prove that each point-generated subframe of � is in �, then the membership in �
of � itself follows immediately from the closure properties of � and the fact that
any frame is a bounded morphic image of the disjoint union of its point-generated
subframes (as the reader was asked to show in Exercise 3.3.4). So from now on we
assume that � is generated by the point �.

�

Now for (one of) the main idea(s) of the proof. Let � be a set of propositional
for each subset � of � . This may
variables containing a propositional variable �
be a huge language: if � is inﬁnite, then � will be uncountable. We will look at
� � �.
the model �

� � � where � is the natural valuation given by � ��

� �

�

�

�

3.8 Advanced Frame Theory

Now let � be the modal type of �; that is, � � �� �
claim that

��

�

�� � �� �

� �

�

� is satisﬁable in �

�

181

��. We

(3.26)

�

�

�

�

� would belong to �

� whence we would have �

In order to prove this, we ﬁrst show that � is ﬁnitely satisﬁable in �. Let � be a
ﬁnite subset of �. It is easy to see that � is satisﬁable in �: if it were not, then
�. (Note that whereas
� is written in a particular language, namely, the one having a proposition letter
� we are not really interested
for each subset of � , when we are talking about �
in a speciﬁc language. This is why we simply assume that ‘�
� would belong
�’ even though we have not veriﬁed that this formula uses only proposition
to �
�. But if
letters that occur in �
each ﬁnite � � � is ﬁnitely satisﬁable in some frame �
in � then � is satisﬁable
in some ultraproduct of these frames (the reader is asked to supply a proof of this
in Exercise 3.8.2 below). Since � is closed under ultraproducts by assumption, this
proves (3.26).

� would contradict that �

�.) But �

� �

�

�

�

�

�

�

�

�

But to say that � is satisﬁable in � amounts to the following. There is a model
� ��� �� � � and a point � in � such that the underlying frame �

� ��� � �

�

�. Since � is closed under (point-)generated subframes and
is in � and �
modal truth is preserved under taking generated subframes, we may assume that
the frame � is generated from �.

� �

�

The only thing left to do is to link up � with our original frame �. This link is

as follows.

�� � is a bounded morphic image of some ultrapower of �

�

(3.27)

�

We ﬁrst ensure the existence of an m-saturated ultrapower of �. Note that we may
���, analogous to the per-
view � as a ﬁrst-order structure for the language �
spective in the previous chapter. Now consider a countably saturated ultrapower of
�.
this ﬁrst-order structure, which we see again as a modal model �
Note that the existence of such an ultrapower is not guaranteed by Lemma 2.73,
may not be countable. We need some heavier
since the ﬁrst-order language �
model-theoretic equipment here; the reader is referred to Theorems 6.1.4 and 6.1.8
� is m-saturated and also has the property that every set �
in [89]. In any case, �
that is ﬁnitely satisﬁable in �

�.
� is satisﬁable in �

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

How are we going to deﬁne the bounded morphism? That is, given an element �
of �
�, which ultraﬁlter over � (the universe of our original frame �) are we going
to assign to it? Recall that an ultraﬁlter over � is some collection of subsets of
� ; this means that given �, we have to decide for each subset of � whether to put
it in � ��� or not. But now it will become clear that there is only one natural choice
for � ���: simply put a subset � of � in � ��� if �

�:
is true at � in the model �

�

� ��� � �� � � �

� �

�

��

�

�

�

�

182

3 Frames

� to ultraﬁlters over � , that �
We will now show that � indeed maps points in �
is a bounded morphism, and that � is onto �� �. In these proofs, the following
equivalence comes in handy:

for all formulas � �

��

�� � ��, �

� iff �

�

�

�

��

(3.28)

The proof of (3.28) is by the following chain of equivalences:

�

�

� �

� �

�

�

�

�

� for all � �

�

�

�

� � � for all � �

�

�

�

� �

�

�

�

�

� for all � �

�

�

�

�

�

�

�

�

�

�

This proves (3.28).

(� is generated from �)
(deﬁnition of �)
(deﬁnition of � and �)
(� is generated from �)
(�

� is an ultrapower of �)

Let us now ﬁrst check that for all � � �

�, � ��� is indeed an ultraﬁlter over � .
We will only check the condition that � ��� is closed under intersection, leaving the
other conditions as exercises for the reader. Suppose that � and � are subsets of �
that both belong to � ���. Hence, by the deﬁnition of � ��� we have that �
and �
the original model �. It then follows from (3.28) that �
particular, this formula is true at �, so we ﬁnd that �
deﬁnition of � , � � � belongs to � ���.

holds throughout
. In
. Hence, by the

. It is easy to see that the formula �

� �

� �

� �

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

�

�

�

�

�

�

�

�

�

�

�

�

�

In order to show that � is a bounded morphism, we will prove that for all ultra-
�, we have that � � � ��� if and only if � (in
ﬁlters � over � and all points � in �
�) satisfy the same formulas. This sufﬁces, by Proposition 2.54
�� �) and � (in �
and the m-saturation of �� � and �
�. The right to left direction of the equivalence
is easy to prove. If the same formulas hold in � and �, then in particular we have for
. But by deﬁnition of the valuation
each � � � that �
� � �. Hence, we ﬁnd that
on �� � we have that �� �

iff � � � ��

iff �� �

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

� �

�

�

iff � � �. This immediately yields � � � ���.

�

�

For the other direction, it sufﬁces to show that for each formula � �

��

�� � ��

�, �� �

and each point � in �
�. Suppose that � holds at
� ��� in �� �. By Proposition 2.59 we have that � ��� � � ���. Thus by deﬁnition
. It follows easily from the deﬁnition of � that
of � we obtain that �
. But then we may

� only if �

� � �

� � �

� � ���

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

�

�

immediately infer that �

, so by (3.28) we have that �
�.

� �

�

�

��

� � � �� is ﬁnitely satisﬁable in �

Finally, we have to show that � is surjective; that is, each ultraﬁlter over �
should belong to its range. Let � be such an ultraﬁlter; we claim that the set � �
�. Let � be a ﬁnite subset of �. To
start with, � is satisﬁable in �. Since � is generated from �, this shows that
� for some natural number �. From the deﬁnition of � and � it
�, so from the fact that � is point-generated from � we

follows that �

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

3.8 Advanced Frame Theory

183

obtain that

� is satisﬁable in �. Now �

� is also satisﬁable in �

�. But �

� is an ultrapower of �, so we have that
� is countably saturated; so �, being ﬁnitely
�. It is then immediate that

�, is satisﬁable in some point � of �

�

satisﬁable in �
� ��� � �.

�

This proves (3.27), but why does that mean that � belongs to �? Here we use the
closure properties of �. Recall that � is the underlying frame of the model � in
which we assumed that the set � is satisﬁable. Since � is in � by assumption, �
belongs to � by closure under ultraproducts; �� � is in � as it is a bounded morphic
image of �

�; and ﬁnally, � is in � since � reﬂects ultraﬁlter extensions. �

�

The following proposition, which is of a rather technical nature, will be put to good
use in Chapter 5.

Proposition 3.63 Let � be a modal similarity type, and � a class of � -frames.
Suppose that � is an ultrapower of the disjoint union
is a family of frames in �. Then � is a bounded morphic image of a disjoint union
of ultraproducts of frames in �.

, where �

� � � � �

�

�

�

�

�

�

�

�

� ��� �� denote the disjoint union

Proof. Let �
, and assume that � is
�, where � is an ultraﬁlter over some index
some ultrapower of �, say �
set �. We assume that � contains only one operator �, of arity �. This allows us
� (that is, the subscript � refers to an index
to write �
element of �, not to an operator from the similarity type).

� ��� �� and �

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

�

�

�

�

Consider an arbitrary state � of �. By the deﬁnition of ultrapowers, there exists

a sequence �

�

�

�

�

�

� such that

�

� � ��

�

� �� �

� � �

�

���

�

�

�

�

�

�

�

As � is the disjoint union of the universes �
element �

� is an element of �

� � such that �

�

��

�

, for each � � � there exists an

. Form the ultraproduct

�

�

�

�

�

Clearly this frame is an ultraproduct of frames in �.

�

�

�

��

�

�

�

�

�

We will now deﬁne a map �

�, and show that �
follows that � is a bounded morphic image of the disjoint union
� is the universe of �. Observe that a typical element of �

to states of the frame
is a bounded morphism with � in its range. From this it easily
, where

sending states of the frame �

has the form

�

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

�

� � �

��

�

�

�

�

�

�

�

�

for some � �
Note that in general these two equivalence classes will not be identical, since �
�. However,
may contain elements � for which ���

� , we have that �

� for some index �

. Since

.

� � � � �

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

184

3 Frames

it is evident that if both � and � are in

, then we ﬁnd that �

�

� iff

� �

�

�

�

�

�

�

� iff �

. This means that if we put

� �

�

�

�

� �

�

�

�

��

� �� �

�

�

�

we have found a well-deﬁned map from the universe of �
(in fact, this map is injective).

�

to the universe � of �

Now consider the element �

�

� . By deﬁnition of the indices �

, we

�

�

�

�

�

must have �

�

�

�

�

�

�

�

�

. It follows that �

�

is in the domain of �

. Now

�

�

�

�

�

�

��

� � ��

�

� ��

�

�

�

�

It remains to be proved that �
straightforward argument using standard properties of ultraﬁlters. �

is a bounded morphism. However, this follows by a

�

Exercises for Section 3.8
3.8.1 Let � be an arbitrary modal similarity type and � a � -frame. Prove that the ultraﬁlter
extension of � is the bounded morphic image of some �-saturated ultrapower of �; in other
words, supply a proof for Theorem 3.17. (Hint: use an argument analogous to one in the
proof of Theorem 3.19. That is, consider a language having a propositional variable �
for
each subset � of the universe of �, and take a countably saturated ultrapower of the model

�

�

�

� �

� �

�, where � is the natural valuation mapping �

to � for each variable �

.)

�

�

3.8.2 Let � be some class of frames, and � a set of formulas which is ﬁnitely satisﬁable
in �. Show that � is satisﬁable in an ultraproduct of frames in �.

3.8.3

(a) Show that the complement of a modally deﬁnable class is closed under taking

ultrapowers.

Now suppose that the class � of frames is deﬁnable by a single formula �.

(b) Show that the complement of � is closed under taking ultraproducts..

�

�

Let �
sense that for any frame � we have that �
the ﬁrst-order theory of �.

� be the set of ﬁrst-order sentences that are semantic consequences of �, in the
� is
� only if �

�. In other words, �

��

�

�

�

�

�

�

(c) Prove that � is a semantic consequence of �

�. Hint: reason by contraposition

�

�

and use (b).

(d) Prove that � is a semantic consequence of a ﬁnite subset of �

�

�. Hint: prove that

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

�, and use compactness.

(e) Conclude that if a modal formula � deﬁnes an elementary frame class, then � cor-

responds to a (single) ﬁrst-order formula.

3.8.4 Prove the strong version of the Goldblatt-Thomason Theorem which applies to any
frame class that is closed under taking ultrapowers.
(Hint: strengthen the result of Exercise 3.8.2 by showing that any set of modal formulas
that is ﬁnitely satisﬁable in a frame class � is itself satisﬁable in an ultrapower of a disjoint
union of frames in �.)

3.9 Summary of Chapter 3

185

3.8.5 Point out where, in the picture summarizing the proof of Theorem 3.19, we use
which closure conditions on �. (For instance: in step 2 we need the fact that � is closed
under taking ultraproducts.)

3.9 Summary of Chapter 3

� Frame Deﬁnability: A modal formula is valid on a frame if and only if it is
satisﬁed at every point in the frame, no matter which valuation is used. A modal
formula deﬁnes a class of frames if and only if it is valid on precisely the frames
in that class.

� Frame Deﬁnability is Second-Order: Because the deﬁnition of validity quan-
tiﬁes across all possible valuations, and because valuations are assignments of
subsets of frames, the concept of validity, and hence frame deﬁnability, is in-
trinsically second-order.

� Frame Languages: Every modal formula can be translated into the appropriate
second-order frame language. Such languages have an �� �-place relation sym-
bol for every �-place modality. Proposition letters correspond to unary predicate
variables. The required translation is called the Second-Order Translation. This
is simply the standard translation modiﬁed to send proposition letters to (unary)
predicate variables rather than predicate constants.

� Correspondence: Sometimes the second-order formulas obtained using this
translation are equivalent to ﬁrst-order formulas. But often they correspond to
genuinely second-order formulas. This can sometimes be shown by exhibiting
a failure of Compactness or the L¨owenhein-Skolem property.

� Frame Constructions: The four fundamental model constructions discussed in
the previous chapter have obvious frame-theoretic counterparts. Moreover, va-
lidity is preserved under the formation of disjoint unions, generated subframes
and bounded morphic images, and anti-preserved under ultraﬁlter extensions.
� Goldblatt-Thomason Theorem: A ﬁrst-order deﬁnable frame class is modally
deﬁnable if and only if it is closed under disjoint unions, generated subframes
and bounded morphic images, and reﬂects ultraﬁlter extensions.

� Modal Deﬁnability on Finite Transitive Frames: A class of ﬁnite transitive
frames is modally deﬁnable if and only if it is preserved under (ﬁnite) disjoint
unions, generated subframes and bounded morphic images.

� The Finite Frame Property: A normal modal logic � has the ﬁnite frame prop-
erty if and only if any formula that does not belong to � can be falsiﬁed on a
ﬁnite frame that validates all the formulas in �. A normal logic has the ﬁnite
frame property if and only if it has the ﬁnite model property.

� The Sahlqvist Fragment: Formulas in the Sahlqvist fragment have the property
that the second-order formula obtained via the Second-Order Translation can

186

3 Frames

be reduced to an equivalent ﬁrst-order formula. The Sahlqvist-Van Benthem
algorithm is an effective procedure for carrying out such reductions.

� Why Sahlqvist Formulas have First-Order Correspondents: Syntactically, the
Sahlqvist fragment forbids universal operators to take scope over existential or
disjunctive connectives in the antecedent. Semantically, this guarantees that we
will always be able to ﬁnd a unique minimal valuation that makes the antecedent
true. This ensures that Sahlqvist formulas have ﬁrst-order correspondents.
� Negative Results: There are non-Sahlqvist formulas that deﬁne ﬁrst-order con-
ditions. Moreover, Chagrova’s Theorem tells us that it is undecidable whether a
modal formula has a ﬁrst-order equivalent.

� Kracht’s Theorem: Kracht’s Theorem takes us back from ﬁrst-order languages
to modal languages. It identiﬁes a class of ﬁrst-order formulas that are the ﬁrst-
order correspondents of Sahlqvist formulas.

� Frames and their Ultraﬁlter Extensions: The ultraﬁlter extension of a frame
may be obtained as a bounded morphic image of an ultrapower of the frame.
� Ultrapowers of Disjoint Unions: Ultrapowers of a disjoint union may be ob-

tained as bounded morphic images of disjoint unions of ultraproducts.

Notes

The study of frames has been central to modal logic since the dawn of the classical
era (see the Historical Overview in Chapter 1), but the way frames have been stud-
ied has changed dramatically over this period. The insight that gave birth to the
classical era was that simple properties of frames (such as transitivity and reﬂex-
ivity) could be used to characterize normal modal logics, and most of the 1960s
were devoted to exploring this topic. It is certainly an important topic. For ex-
ample, in the ﬁrst half of the following chapter we will see that most commonly
encountered modal logics can be given simple, intuitively appealing, frame-based
characterizations. But the very success of this line of work meant that for a decade
modal logicians paid little attention to modal languages as tools for describing
frame structure. Frames were simply tools for analyzing normal logics. The notion
of frame deﬁnability, and the systematic study of modal expressivity over frames,
only emerged as a research theme after the frame incompleteness results showed
that not all normal logics could be given frame-based characterizations. The ﬁrst
incompleteness result (shown for the basic temporal language) was published in
1972 by S.K. Thomason [426]. The ﬁrst incompleteness results for the basic modal
language were published in 1974 by S.K. Thomason [427] and Kit Fine [137].

The frame incompleteness theorems and the results which accompanied them
decisively changed the research agenda of modal logic, essentially because they
made it clear that the modal perspective on frames was intrinsically second-order.
We’ve seen ample evidence for this in this chapter: as we saw in Example 3.11

3.9 Summary of Chapter 3

187

��

� �

� deﬁnes a non-
a formula as innocuous looking as McKinsey’s ��
elementary class of frames. This was proved independently by Goldblatt [189]
and van Benthem [34]. The proof given in the text is from Theorem 10.2 of van
Benthem [41]. It was shown by S.K. Thomason [428] that on the level of frames,
modal logic is expressive enough to capture the semantic consequence relation for
�. Moreover, in unpublished work, Doets showed showed that modal formulas
can act as a reduction class for the the theory of ﬁnite types; see Benthem [41,
23–24] for further discussion.

�

So by the mid 1970s it was clear that modal logic embodied a substantial frag-
ment of second-order logic, and a radically different research program was well
under way. One strand of this program was algebraic: these years saw the (re)-
emergence of algebraic semantics together with a belated appreciation of the work
of J´onsson and Tarski [260, 261]; this line of work is treated in Chapter 5. The
other strand was the emergence of correspondence theory.

Given that modal logic over frames is essentially second-order logic in disguise,
it may seem that the most obvious way to develop correspondence theory would be
to chart the second-order powers of modal logic. In fact, examples of modal for-
mulas that deﬁne second-order classes of frames were known by the early 1970s
(for example, Johan van Benthem proved that the L¨ob formula deﬁned the class
of transitive and converse well-founded frames using the argument given in Exam-
ple 3.9). And there is interesting work on more general results on second-order
frame deﬁnability, much of which may be found in Chapters XVII–XIX of van
Benthem [41]. Nonetheless, most work on correspondence theory for frames has
concentrated on its ﬁrst-order aspects. There are two main reasons for this. First,
second-order model theory is less well understood than ﬁrst-order model theory, so
investigations of second-order correspondences have fewer useful results to draw
on. Second, there is a clear sense that it is the ﬁrst-order aspects of frame deﬁn-
ability which are truly mysterious (this has long been emphasized by Johan van
Benthem). With the beneﬁt of hindsight, the second-order nature of validity is ob-
vious; understanding when — and why — it’s sometimes ﬁrst-order is far harder.
In this chapter we examined the two main strands in ﬁrst-order correspondence
theory (for frames): the semantic, exempliﬁed by the Goldblatt-Thomason Theo-
rem, and the syntactic exempliﬁed by the Sahlqvist Correspondence Theorem. (In-
cidentally, as we will learn in Chapter 5, both results have a substantial algebraic
dimension.)

What we call the Goldblatt-Thomason Theorem was actually proved by Gold-
blatt. His result was in fact stronger than our Theorem 3.19, applying to any frame
class that is closed under elementary equivalence. This theorem was published in
a joint paper [194] with S.K. Thomason, who added a more general result which
applies to all deﬁnable frame classes but has a less appealing frame construction.
The model-theoretic proof of the theorem that we supplied in this chapter is due

188

3 Frames

to van Benthem [45], who also proved the ﬁnite transitive version we recorded as
Theorem 3.21. Barwise and Moss [27] obtain correspondence results for models
as opposed to frames; their main result is that if a modal formula � has a ﬁrst-
, then for all models �, � satisﬁes all substitution
order frame correspondent �
instances of � in inﬁnitary modal logic iff a certain frame underlying � satisﬁes

�

�

�

.
Concerning the identiﬁcation of syntactic classes of modal formulas that corre-
spond to ﬁrst-order formulas, Sahlqvist’s result was not the ﬁrst. As early as in the
J´onsson-Tarski papers [260, 261] particular examples such as reﬂexivity and transi-
tivity were known. And an article by Fitch [144] was a stimulus for van Benthem’s
investigations in this area, which lead to van Benthem (unaware of Sahlqvist’s ear-
lier work) proving what is now known as Sahlqvist’s theorem. But Sahlqvist’s
paper [388] (essentially a presentation of results contained in his Master’s thesis)
remains the classic reference in the area. It greatly generalized all previous known
results in the area and drew a beautiful link between deﬁnability and completeness.
Kracht isolated the ﬁrst-order formulas that are the correspondents of Sahlqvist
formulas in [282], as an application of his so-called calculus of internal describa-
bility. This calculus relates modal and ﬁrst-order formulas on the level of general
frames; see also [286].

During the 1990s a number of alternative correspondence languages have been
considered for the basic modal language. In the so-called functional translation
the accessibility relations are replaced by certain terms which can be seen as func-
tions mapping worlds to accessible worlds. From a certain point of view this func-
tional language is more expressive than the relational language, and that certain
second-order frame properties can be mapped to formulas expressed in the func-
tional language — but this is not too surprising: in the functional language one can
quantify over functions; this additional expressive power allows one to do without
quantiﬁcation over unary predicate variables; see Ohlbach et al. [350, 349] and
Simmons [407].

As with ﬁnite model theory, the theory of ﬁnite frames is rather underdeveloped.
However some of the basic results have been known a long time. We showed in
Theorem 3.28 that a normal logic has the ﬁnite model property if and only if it has
the ﬁnite frame property. This result is due to Segerberg [396, Corollary 3.8, page
33]. For some interesting results concerning frame correspondence theory over the
class of ﬁnite frames the reader should consult the dissertation of Doets [118].

To conclude these Notes, we’ll tidy up a few loose ends. Example 3.6.2 is due to
van Benthem [41, Theorem 10.4]. Exercise 3.2.4 is based on a result in Fine [140].
Second, we mentioned Chagrova’s theorem [87] that it is undecidable whether a
modal formula has a ﬁrst-order equivalent. For pointers to, and a brief discussion
of, extensions of this line of work, see Chagrov and Zakharyaschev [86, Chap-
ter 17]. At the end of Section 3.2 we remarked that general frames can be seen

3.9 Summary of Chapter 3

189

as a model version of the generalized models or Henkin models for second-order
logic. Henkin [222] introduced such models, and good discussions of them can be
found in Doets and van Benthem [120] or Manzano [320]. Finally, for more on the
lambda calculus see Barendregt [23] or Hindley and Seldin [229].


