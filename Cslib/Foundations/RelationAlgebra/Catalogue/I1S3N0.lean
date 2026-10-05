/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra02
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra03
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra04
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra05
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra06
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra07
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra08
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra09
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra10
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra11
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra12
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra13
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra14
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra15
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra16
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra17
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra18
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra19
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra20
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra21
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra22
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra23
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra24
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra25
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra26
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra27
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra28
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra29
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra30
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra31
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra32
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra33
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra34
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra35
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra36
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra37
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra38
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra39
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra40
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra41
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra42
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra43
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra44
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra45
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra46
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra47
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra48
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra49
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra50
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra51
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra52
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra53
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra54
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra55
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra56
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra57
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra58
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra59
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra60
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra61
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra62
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra63
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra64
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra65
public import Cslib.Foundations.RelationAlgebra.FastClassification

/-!
# Classification of the ⟨1, 3, 0⟩ catalogue row

This row contains 65 isomorphism classes, of which 45 are representable and
20 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
Ten Peircean cycle orbits reduce this classification to 1024 possible cycle tables.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0

/-- The certified cycle tables, in the source's order. -/
def table : Fin 65 → IntegralCycleTable 3 0
  | ⟨0, _⟩ => Ra01.table
  | ⟨1, _⟩ => Ra02.table
  | ⟨2, _⟩ => Ra03.table
  | ⟨3, _⟩ => Ra04.table
  | ⟨4, _⟩ => Ra05.table
  | ⟨5, _⟩ => Ra06.table
  | ⟨6, _⟩ => Ra07.table
  | ⟨7, _⟩ => Ra08.table
  | ⟨8, _⟩ => Ra09.table
  | ⟨9, _⟩ => Ra10.table
  | ⟨10, _⟩ => Ra11.table
  | ⟨11, _⟩ => Ra12.table
  | ⟨12, _⟩ => Ra13.table
  | ⟨13, _⟩ => Ra14.table
  | ⟨14, _⟩ => Ra15.table
  | ⟨15, _⟩ => Ra16.table
  | ⟨16, _⟩ => Ra17.table
  | ⟨17, _⟩ => Ra18.table
  | ⟨18, _⟩ => Ra19.table
  | ⟨19, _⟩ => Ra20.table
  | ⟨20, _⟩ => Ra21.table
  | ⟨21, _⟩ => Ra22.table
  | ⟨22, _⟩ => Ra23.table
  | ⟨23, _⟩ => Ra24.table
  | ⟨24, _⟩ => Ra25.table
  | ⟨25, _⟩ => Ra26.table
  | ⟨26, _⟩ => Ra27.table
  | ⟨27, _⟩ => Ra28.table
  | ⟨28, _⟩ => Ra29.table
  | ⟨29, _⟩ => Ra30.table
  | ⟨30, _⟩ => Ra31.table
  | ⟨31, _⟩ => Ra32.table
  | ⟨32, _⟩ => Ra33.table
  | ⟨33, _⟩ => Ra34.table
  | ⟨34, _⟩ => Ra35.table
  | ⟨35, _⟩ => Ra36.table
  | ⟨36, _⟩ => Ra37.table
  | ⟨37, _⟩ => Ra38.table
  | ⟨38, _⟩ => Ra39.table
  | ⟨39, _⟩ => Ra40.table
  | ⟨40, _⟩ => Ra41.table
  | ⟨41, _⟩ => Ra42.table
  | ⟨42, _⟩ => Ra43.table
  | ⟨43, _⟩ => Ra44.table
  | ⟨44, _⟩ => Ra45.table
  | ⟨45, _⟩ => Ra46.table
  | ⟨46, _⟩ => Ra47.table
  | ⟨47, _⟩ => Ra48.table
  | ⟨48, _⟩ => Ra49.table
  | ⟨49, _⟩ => Ra50.table
  | ⟨50, _⟩ => Ra51.table
  | ⟨51, _⟩ => Ra52.table
  | ⟨52, _⟩ => Ra53.table
  | ⟨53, _⟩ => Ra54.table
  | ⟨54, _⟩ => Ra55.table
  | ⟨55, _⟩ => Ra56.table
  | ⟨56, _⟩ => Ra57.table
  | ⟨57, _⟩ => Ra58.table
  | ⟨58, _⟩ => Ra59.table
  | ⟨59, _⟩ => Ra60.table
  | ⟨60, _⟩ => Ra61.table
  | ⟨61, _⟩ => Ra62.table
  | ⟨62, _⟩ => Ra63.table
  | ⟨63, _⟩ => Ra64.table
  | ⟨64, _⟩ => Ra65.table
  | ⟨n + 65, h⟩ => False.elim (by omega)

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 65) : Type := Complex (table idx)

private def cycleReps : Fin 10 → Cycle 3 0
  | 0 => (.inl 0, .inl 0, .inl 0)
  | 1 => (.inl 0, .inl 0, .inl 1)
  | 2 => (.inl 0, .inl 0, .inl 2)
  | 3 => (.inl 0, .inl 1, .inl 1)
  | 4 => (.inl 0, .inl 1, .inl 2)
  | 5 => (.inl 0, .inl 2, .inl 2)
  | 6 => (.inl 1, .inl 1, .inl 1)
  | 7 => (.inl 1, .inl 1, .inl 2)
  | 8 => (.inl 1, .inl 2, .inl 2)
  | 9 => (.inl 2, .inl 2, .inl 2)

private theorem cycleReps_cover : ∀ c : Cycle 3 0,
    ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (cycleReps i) := by
  decide +kernel

private def permutation : Fin 6 → Fin 3 → Fin 3
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 1, 0 => 0
  | 1, 1 => 2
  | 1, 2 => 1
  | 2, 0 => 1
  | 2, 1 => 0
  | 2, 2 => 2
  | 3, 0 => 1
  | 3, 1 => 2
  | 3, 2 => 0
  | 4, 0 => 2
  | 4, 1 => 0
  | 4, 2 => 1
  | 5, 0 => 2
  | 5, 1 => 1
  | 5, 2 => 0

private def rename (p : Fin 6) : Atom 3 0 → Atom 3 0
  | none => none
  | some (.inl x) => some (.inl (permutation p x))
  | some (.inr (x, _)) => Fin.elim0 x

private abbrev cycleMask (bits : Fin 10 → Bool) : ℕ := choiceMask bits

private def classificationWitness (mask : ℕ) : Fin 65 × Fin 6 :=
  match mask with
  | 16 => (0, 0)
  | 25 => (1, 3)
  | 49 => (1, 2)
  | 57 => (6, 4)
  | 63 => (7, 4)
  | 82 => (1, 5)
  | 91 => (2, 3)
  | 119 => (4, 4)
  | 127 => (8, 4)
  | 134 => (10, 5)
  | 135 => (14, 5)
  | 140 => (10, 3)
  | 141 => (12, 3)
  | 142 => (20, 3)
  | 143 => (22, 3)
  | 168 => (10, 1)
  | 169 => (11, 1)
  | 172 => (41, 0)
  | 173 => (42, 0)
  | 178 => (29, 1)
  | 179 => (30, 1)
  | 182 => (33, 2)
  | 183 => (35, 2)
  | 186 => (33, 5)
  | 187 => (37, 5)
  | 190 => (49, 5)
  | 191 => (53, 5)
  | 198 => (12, 5)
  | 199 => (16, 5)
  | 204 => (14, 3)
  | 205 => (16, 3)
  | 206 => (22, 5)
  | 207 => (24, 3)
  | 232 => (14, 1)
  | 233 => (15, 1)
  | 236 => (43, 0)
  | 237 => (44, 0)
  | 242 => (30, 2)
  | 243 => (31, 2)
  | 246 => (34, 2)
  | 247 => (36, 2)
  | 250 => (35, 5)
  | 251 => (39, 5)
  | 254 => (51, 5)
  | 255 => (55, 5)
  | 262 => (10, 4)
  | 263 => (14, 4)
  | 284 => (29, 0)
  | 285 => (30, 0)
  | 286 => (33, 3)
  | 287 => (35, 3)
  | 290 => (10, 2)
  | 291 => (12, 2)
  | 294 => (20, 2)
  | 295 => (22, 2)
  | 296 => (10, 0)
  | 297 => (11, 0)
  | 298 => (41, 1)
  | 299 => (42, 1)
  | 316 => (33, 4)
  | 317 => (37, 4)
  | 318 => (49, 4)
  | 319 => (53, 4)
  | 326 => (11, 4)
  | 327 => (15, 4)
  | 336 => (1, 0)
  | 338 => (6, 1)
  | 348 => (30, 4)
  | 349 => (31, 0)
  | 350 => (37, 3)
  | 351 => (39, 3)
  | 354 => (11, 2)
  | 355 => (13, 2)
  | 358 => (21, 2)
  | 359 => (23, 2)
  | 360 => (12, 0)
  | 361 => (13, 0)
  | 362 => (42, 4)
  | 363 => (45, 1)
  | 371 => (18, 2)
  | 374 => (26, 2)
  | 375 => (27, 2)
  | 377 => (18, 0)
  | 379 => (47, 1)
  | 380 => (34, 4)
  | 381 => (38, 4)
  | 382 => (50, 4)
  | 383 => (54, 4)
  | 390 => (41, 2)
  | 391 => (43, 2)
  | 412 => (33, 0)
  | 413 => (34, 0)
  | 414 => (49, 3)
  | 415 => (51, 3)
  | 424 => (20, 0)
  | 425 => (21, 0)
  | 430 => (57, 0)
  | 431 => (58, 0)
  | 434 => (33, 1)
  | 435 => (34, 1)
  | 438 => (49, 2)
  | 439 => (51, 2)
  | 441 => (26, 0)
  | 442 => (49, 1)
  | 443 => (50, 1)
  | 444 => (49, 0)
  | 445 => (50, 0)
  | 446 => (61, 0)
  | 447 => (62, 0)
  | 454 => (42, 2)
  | 455 => (44, 2)
  | 473 => (4, 1)
  | 474 => (7, 1)
  | 475 => (8, 1)
  | 476 => (35, 0)
  | 477 => (36, 0)
  | 478 => (53, 3)
  | 479 => (55, 3)
  | 488 => (22, 0)
  | 489 => (23, 0)
  | 494 => (58, 2)
  | 495 => (59, 0)
  | 498 => (37, 1)
  | 499 => (38, 1)
  | 502 => (50, 2)
  | 503 => (52, 2)
  | 505 => (27, 0)
  | 506 => (53, 1)
  | 507 => (54, 1)
  | 508 => (51, 0)
  | 509 => (52, 0)
  | 510 => (62, 2)
  | 511 => (63, 0)
  | 532 => (1, 4)
  | 543 => (4, 5)
  | 565 => (2, 2)
  | 575 => (8, 5)
  | 599 => (3, 4)
  | 607 => (5, 5)
  | 631 => (5, 4)
  | 639 => (9, 4)
  | 646 => (11, 5)
  | 647 => (15, 5)
  | 652 => (11, 3)
  | 653 => (13, 3)
  | 654 => (21, 3)
  | 655 => (23, 3)
  | 656 => (1, 1)
  | 660 => (6, 0)
  | 669 => (18, 3)
  | 670 => (26, 3)
  | 671 => (27, 3)
  | 680 => (12, 1)
  | 681 => (13, 1)
  | 684 => (42, 5)
  | 685 => (45, 0)
  | 690 => (30, 5)
  | 691 => (31, 1)
  | 694 => (37, 2)
  | 695 => (39, 2)
  | 697 => (18, 1)
  | 698 => (34, 5)
  | 699 => (38, 5)
  | 701 => (47, 0)
  | 702 => (50, 5)
  | 703 => (54, 5)
  | 710 => (13, 5)
  | 711 => (17, 5)
  | 716 => (15, 3)
  | 717 => (17, 3)
  | 718 => (23, 5)
  | 719 => (25, 3)
  | 726 => (18, 5)
  | 727 => (19, 5)
  | 729 => (3, 1)
  | 730 => (4, 3)
  | 731 => (5, 3)
  | 733 => (19, 3)
  | 734 => (27, 5)
  | 735 => (28, 3)
  | 744 => (16, 1)
  | 745 => (17, 1)
  | 748 => (44, 5)
  | 749 => (46, 0)
  | 754 => (31, 5)
  | 755 => (32, 1)
  | 758 => (38, 2)
  | 759 => (40, 2)
  | 761 => (19, 1)
  | 762 => (36, 5)
  | 763 => (40, 5)
  | 765 => (48, 0)
  | 766 => (52, 5)
  | 767 => (56, 5)
  | 774 => (12, 4)
  | 775 => (16, 4)
  | 796 => (30, 3)
  | 797 => (31, 3)
  | 798 => (34, 3)
  | 799 => (36, 3)
  | 802 => (14, 2)
  | 803 => (16, 2)
  | 806 => (22, 4)
  | 807 => (24, 2)
  | 808 => (14, 0)
  | 809 => (15, 0)
  | 810 => (43, 1)
  | 811 => (44, 1)
  | 828 => (35, 4)
  | 829 => (39, 4)
  | 830 => (51, 4)
  | 831 => (55, 4)
  | 838 => (13, 4)
  | 839 => (17, 4)
  | 854 => (18, 4)
  | 855 => (19, 4)
  | 860 => (31, 4)
  | 861 => (32, 0)
  | 862 => (38, 3)
  | 863 => (40, 3)
  | 866 => (15, 2)
  | 867 => (17, 2)
  | 870 => (23, 4)
  | 871 => (25, 2)
  | 872 => (16, 0)
  | 873 => (17, 0)
  | 874 => (44, 4)
  | 875 => (46, 1)
  | 881 => (3, 0)
  | 883 => (19, 2)
  | 884 => (4, 2)
  | 885 => (5, 2)
  | 886 => (27, 4)
  | 887 => (28, 2)
  | 889 => (19, 0)
  | 891 => (48, 1)
  | 892 => (36, 4)
  | 893 => (40, 4)
  | 894 => (52, 4)
  | 895 => (56, 4)
  | 902 => (42, 3)
  | 903 => (44, 3)
  | 924 => (37, 0)
  | 925 => (38, 0)
  | 926 => (50, 3)
  | 927 => (52, 3)
  | 936 => (22, 1)
  | 937 => (23, 1)
  | 942 => (58, 3)
  | 943 => (59, 1)
  | 945 => (4, 0)
  | 946 => (35, 1)
  | 947 => (36, 1)
  | 948 => (7, 0)
  | 949 => (8, 0)
  | 950 => (53, 2)
  | 951 => (55, 2)
  | 953 => (27, 1)
  | 954 => (51, 1)
  | 955 => (52, 1)
  | 956 => (53, 0)
  | 957 => (54, 0)
  | 958 => (62, 3)
  | 959 => (63, 1)
  | 966 => (45, 2)
  | 967 => (46, 2)
  | 976 => (2, 0)
  | 982 => (47, 2)
  | 983 => (48, 2)
  | 985 => (5, 1)
  | 986 => (8, 3)
  | 987 => (9, 1)
  | 988 => (39, 0)
  | 989 => (40, 0)
  | 990 => (54, 3)
  | 991 => (56, 3)
  | 1000 => (24, 0)
  | 1001 => (25, 0)
  | 1006 => (59, 4)
  | 1007 => (60, 0)
  | 1009 => (5, 0)
  | 1010 => (39, 1)
  | 1011 => (40, 1)
  | 1012 => (8, 2)
  | 1013 => (9, 0)
  | 1014 => (54, 2)
  | 1015 => (56, 2)
  | 1017 => (28, 0)
  | 1018 => (55, 1)
  | 1019 => (56, 1)
  | 1020 => (55, 0)
  | 1021 => (56, 0)
  | 1022 => (63, 4)
  | 1023 => (64, 0)
  | _ => (0, 0)

-- Each row packs the six 10-bit cycle profiles, one for each atom renaming.
private def profileRowCode : Fin 65 → ℕ
  | 0 => 18032007892189200
  | 1 => 92908759442669904
  | 2 => 103078213896324048
  | 3 => 675073435346102129
  | 4 => 611495276058208177
  | 5 => 684115821124872177
  | 6 => 64239330469956244
  | 7 => 71001473311796148
  | 8 => 647533144182321077
  | 9 => 720153689248985077
  | 10 => 151158810191503656
  | 11 => 727690481062028585
  | 12 => 223779355258167656
  | 13 => 800311026128692585
  | 14 => 152285878866387752
  | 15 => 728817549736912681
  | 16 => 224906423933051752
  | 17 => 801438094803576681
  | 18 => 818343034020881785
  | 19 => 819470102695765881
  | 20 => 160201195970273704
  | 21 => 736732866840798633
  | 22 => 232821741036937704
  | 23 => 809353411907462633
  | 24 => 233948809711821800
  | 25 => 810480480582346729
  | 26 => 754764874732987833
  | 27 => 827385419799651833
  | 28 => 828512488474535929
  | 29 => 200722749849782556
  | 30 => 777254420720307485
  | 31 => 849874965786971485
  | 32 => 851002034461855581
  | 33 => 209765135628552604
  | 34 => 786296806499077533
  | 35 => 282385680695216604
  | 36 => 858917351565741533
  | 37 => 210892204303436700
  | 38 => 787423875173961629
  | 39 => 283512749370100700
  | 40 => 860044420240625629
  | 41 => 193982857610569900
  | 42 => 770514528481094829
  | 43 => 266603402677233900
  | 44 => 843135073547758829
  | 45 => 771641597155978925
  | 46 => 844262142222642925
  | 47 => 789673605048168125
  | 48 => 862294150114832125
  | 49 => 214271071986575804
  | 50 => 790802742857100733
  | 51 => 286891617053239804
  | 52 => 863423287923764733
  | 53 => 215398140661459900
  | 54 => 791929811531984829
  | 55 => 288018685728123900
  | 56 => 864550356598648829
  | 57 => 484610212102584750
  | 58 => 1061141882973109679
  | 59 => 1133762428039773679
  | 60 => 1134889496714657775
  | 61 => 502642219994773950
  | 62 => 1079173890865298879
  | 63 => 1151794435931962879
  | 64 => 1152921504606846975
  | ⟨n + 65, h⟩ => False.elim (by omega)

private def profileCode (i : Fin 65) (p : Fin 6) : ℕ :=
  Code.field (profileRowCode i) (10 * p.val) 10

private def modelCode : Fin 65 → ℕ
  | 0 => 1317339743034442785
  | 1 => 6505631649300120609
  | 2 => 16017313227143808033
  | 3 => 18070875494537135137
  | 4 => 18359180637479535649
  | 5 => 18359185035526046753
  | 6 => 10838028520678130721
  | 7 => 18368187837277439009
  | 8 => 18368187837279536161
  | 9 => 18368192235326047265
  | 10 => 8685336211680822305
  | 11 => 8685336211682919457
  | 12 => 8685340609727333409
  | 13 => 8685340609729430561
  | 14 => 17908708248535598113
  | 15 => 17908708248537695265
  | 16 => 17908712646582109217
  | 17 => 17908712646584206369
  | 18 => 8847505931650630689
  | 19 => 18070877968505406497
  | 20 => 8973645752669733921
  | 21 => 8973645752671831073
  | 22 => 8973650150716245025
  | 23 => 8973650150718342177
  | 24 => 18197022187571020833
  | 25 => 18197022187573117985
  | 26 => 9135811074593031201
  | 27 => 9135815472639542305
  | 28 => 18359187509494318113
  | 29 => 6514636925021881377
  | 30 => 6514636925023978529
  | 31 => 6514641323070489633
  | 32 => 15738013359925265441
  | 33 => 6802946466010792993
  | 34 => 6802946466012890145
  | 35 => 6802950864057304097
  | 36 => 6802950864059401249
  | 37 => 16026318502865568801
  | 38 => 16026318502867665953
  | 39 => 16026322900912079905
  | 40 => 16026322900914177057
  | 41 => 3794365444250567713
  | 42 => 3794365444252664865
  | 43 => 3794369842297078817
  | 44 => 3794369842299175969
  | 45 => 13017737481107440673
  | 46 => 13017741879153951777
  | 47 => 13179902803028640801
  | 48 => 13179907201075151905
  | 49 => 9144818274390934561
  | 50 => 9144818274393031713
  | 51 => 9144822672437445665
  | 52 => 9144822672439542817
  | 53 => 18368190311245710369
  | 54 => 18368190311247807521
  | 55 => 18368194709292221473
  | 56 => 18368194709294318625
  | 57 => 8982653089946436641
  | 58 => 8982653089948533793
  | 59 => 8982657487995044897
  | 60 => 18206029524849820705
  | 61 => 9144818411867636769
  | 62 => 9144818411869733921
  | 63 => 9144822809916245025
  | 64 => 18368194846771020833
  | ⟨n + 65, h⟩ => False.elim (by omega)

private theorem modelCode_eq : ∀ i, tableCode (table i).cycles = modelCode i := by
  decide +kernel

private theorem modelCode_encodes (i : Fin 65) : EncodesTable (table i).cycles (modelCode i) := by
  rw [← modelCode_eq]
  exact encodesTable_tableCode _

private def renameCode : Fin 6 → ℕ → ℕ
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 3
  | 1, 3 => 2
  | 2, 0 => 0
  | 2, 1 => 2
  | 2, 2 => 1
  | 2, 3 => 3
  | 3, 0 => 0
  | 3, 1 => 2
  | 3, 2 => 3
  | 3, 3 => 1
  | 4, 0 => 0
  | 4, 1 => 3
  | 4, 2 => 1
  | 4, 3 => 2
  | 5, 0 => 0
  | 5, 1 => 3
  | 5, 2 => 2
  | 5, 3 => 1
  | _, _ => 0

private theorem renameCode_eq : ∀ p x, (rename p x).code = renameCode p x.code := by
  decide +kernel

private theorem rename_laws : ∀ p, Function.Injective (rename p) ∧ rename p none = none ∧
    ∀ x, rename p x.converse = (rename p x).converse := by
  decide +kernel

private theorem renamings_exhaustive : ∀ f : Atom 3 0 → Atom 3 0,
    Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ p : Fin 6, f = rename p := by
  unfold Function.Injective
  decide +kernel

private theorem rename_zero : ∀ x, rename 0 x = x := by
  decide +kernel

private theorem profileCode_eq : ∀ idx : Fin 65, ∀ p : Fin 6,
    cycleMask (fun c => decide (cycleClosure (table idx).cycles
      (rename p (some (cycleReps c).1)) (rename p (some (cycleReps c).2.1))
      (rename p (some (cycleReps c).2.2)))) = profileCode idx p := by
  simp only [cycleClosure_iff_bitAt (modelCode_encodes _), Bool.decide_eq_true, renameCode_eq]
  decide +kernel

private theorem cycleReps_distinct : ∀ i l,
    (some (cycleReps i).1, some (cycleReps i).2.1, some (cycleReps i).2.2) ∈
      cycleOrbit (cycleReps l) ↔ i = l := by
  decide +kernel

private def orbitMask : ℕ → ℕ
  | 0 => 2097152
  | 1 => 137476702208
  | 2 => 9007199800000512
  | 3 => 2473968271360
  | 4 => 162165321921200128
  | 5 => 2341871808380141568
  | 6 => 4398046511104
  | 7 => 288309540988911616
  | 8 => 5188287508219166720
  | 9 => 9223372036854775808
  | _ => 0

private def choiceCode (mask : ℕ) : ℕ :=
  Nat.lor 1155174421113242657 (Code.orBelow (fun i => cond (Code.bitAt mask i) (orbitMask i) 0) 10)

private theorem cycleChoiceCode_eq : cycleChoiceCode cycleReps = choiceCode := by rfl

set_option maxRecDepth 4096 in
private theorem cycles_exhaustive : ∀ bits : Fin 10 → Bool,
    AtomCompositionAssociative (selectedCycles cycleReps bits) →
      ∃ idx : Fin 65, ∃ f,
        AtomRelabelling (selectedCycles cycleReps bits) (table idx).cycles f := by
  apply cycles_exhaustive_of_profileCheck cycleReps cycleReps_cover cycleReps_distinct
    table rename rename_laws profileCode profileCode_eq classificationWitness
  rw [cycleChoiceCode_eq]
  decide +kernel

private theorem profileCode_injective : ∀ i j : Fin 65, ∀ p : Fin 6,
    profileCode i 0 = profileCode j p → i = j := by
  exact profileCode_injective_of_check profileCode 0 (by decide +kernel)

private theorem cycles_distinct : ∀ i j : Fin 65, ∀ f,
    AtomRelabelling (table i).cycles (table j).cycles f → i = j := by
  intro i j f hf
  obtain ⟨p, rfl⟩ := renamings_exhaustive f hf.1 hf.2.1 hf.2.2.1
  apply profileCode_injective i j p
  rw [← profileCode_eq i 0, ← profileCode_eq j p]
  simp only [rename_zero]
  congr 1
  funext c
  simp only [hf.2.2.2]

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 3 0) :
    ∃! idx : Fin 65, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  exact classification_of_cycle_basis cycleReps cycleReps_cover table
    cycles_exhaustive cycles_distinct A h

private def nonrepresentableIndices : Finset (Fin 65) :=
  {18, 19, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 47, 48, 49, 51, 52, 57, 58, 59}

private theorem model_representable_iff : ∀ idx : Fin 65,
    Representable (Model idx) ↔ idx ∉ nonrepresentableIndices
  | ⟨0, _⟩ => iff_of_true Ra01.representable (by decide +kernel +revert)
  | ⟨1, _⟩ => iff_of_true Ra02.representable (by decide +kernel +revert)
  | ⟨2, _⟩ => iff_of_true Ra03.representable (by decide +kernel +revert)
  | ⟨3, _⟩ => iff_of_true Ra04.representable (by decide +kernel +revert)
  | ⟨4, _⟩ => iff_of_true Ra05.representable (by decide +kernel +revert)
  | ⟨5, _⟩ => iff_of_true Ra06.representable (by decide +kernel +revert)
  | ⟨6, _⟩ => iff_of_true Ra07.representable (by decide +kernel +revert)
  | ⟨7, _⟩ => iff_of_true Ra08.representable (by decide +kernel +revert)
  | ⟨8, _⟩ => iff_of_true Ra09.representable (by decide +kernel +revert)
  | ⟨9, _⟩ => iff_of_true Ra10.representable (by decide +kernel +revert)
  | ⟨10, _⟩ => iff_of_true Ra11.representable (by decide +kernel +revert)
  | ⟨11, _⟩ => iff_of_true Ra12.representable (by decide +kernel +revert)
  | ⟨12, _⟩ => iff_of_true Ra13.representable (by decide +kernel +revert)
  | ⟨13, _⟩ => iff_of_true Ra14.representable (by decide +kernel +revert)
  | ⟨14, _⟩ => iff_of_true Ra15.representable (by decide +kernel +revert)
  | ⟨15, _⟩ => iff_of_true Ra16.representable (by decide +kernel +revert)
  | ⟨16, _⟩ => iff_of_true Ra17.representable (by decide +kernel +revert)
  | ⟨17, _⟩ => iff_of_true Ra18.representable (by decide +kernel +revert)
  | ⟨18, _⟩ => iff_of_false Ra19.not_representable (by decide +kernel +revert)
  | ⟨19, _⟩ => iff_of_false Ra20.not_representable (by decide +kernel +revert)
  | ⟨20, _⟩ => iff_of_true Ra21.representable (by decide +kernel +revert)
  | ⟨21, _⟩ => iff_of_true Ra22.representable (by decide +kernel +revert)
  | ⟨22, _⟩ => iff_of_true Ra23.representable (by decide +kernel +revert)
  | ⟨23, _⟩ => iff_of_true Ra24.representable (by decide +kernel +revert)
  | ⟨24, _⟩ => iff_of_true Ra25.representable (by decide +kernel +revert)
  | ⟨25, _⟩ => iff_of_true Ra26.representable (by decide +kernel +revert)
  | ⟨26, _⟩ => iff_of_true Ra27.representable (by decide +kernel +revert)
  | ⟨27, _⟩ => iff_of_true Ra28.representable (by decide +kernel +revert)
  | ⟨28, _⟩ => iff_of_true Ra29.representable (by decide +kernel +revert)
  | ⟨29, _⟩ => iff_of_true Ra30.representable (by decide +kernel +revert)
  | ⟨30, _⟩ => iff_of_false Ra31.not_representable (by decide +kernel +revert)
  | ⟨31, _⟩ => iff_of_false Ra32.not_representable (by decide +kernel +revert)
  | ⟨32, _⟩ => iff_of_false Ra33.not_representable (by decide +kernel +revert)
  | ⟨33, _⟩ => iff_of_false Ra34.not_representable (by decide +kernel +revert)
  | ⟨34, _⟩ => iff_of_false Ra35.not_representable (by decide +kernel +revert)
  | ⟨35, _⟩ => iff_of_false Ra36.not_representable (by decide +kernel +revert)
  | ⟨36, _⟩ => iff_of_false Ra37.not_representable (by decide +kernel +revert)
  | ⟨37, _⟩ => iff_of_false Ra38.not_representable (by decide +kernel +revert)
  | ⟨38, _⟩ => iff_of_false Ra39.not_representable (by decide +kernel +revert)
  | ⟨39, _⟩ => iff_of_true Ra40.representable (by decide +kernel +revert)
  | ⟨40, _⟩ => iff_of_false Ra41.not_representable (by decide +kernel +revert)
  | ⟨41, _⟩ => iff_of_true Ra42.representable (by decide +kernel +revert)
  | ⟨42, _⟩ => iff_of_true Ra43.representable (by decide +kernel +revert)
  | ⟨43, _⟩ => iff_of_true Ra44.representable (by decide +kernel +revert)
  | ⟨44, _⟩ => iff_of_true Ra45.representable (by decide +kernel +revert)
  | ⟨45, _⟩ => iff_of_true Ra46.representable (by decide +kernel +revert)
  | ⟨46, _⟩ => iff_of_true Ra47.representable (by decide +kernel +revert)
  | ⟨47, _⟩ => iff_of_false Ra48.not_representable (by decide +kernel +revert)
  | ⟨48, _⟩ => iff_of_false Ra49.not_representable (by decide +kernel +revert)
  | ⟨49, _⟩ => iff_of_false Ra50.not_representable (by decide +kernel +revert)
  | ⟨50, _⟩ => iff_of_true Ra51.representable (by decide +kernel +revert)
  | ⟨51, _⟩ => iff_of_false Ra52.not_representable (by decide +kernel +revert)
  | ⟨52, _⟩ => iff_of_false Ra53.not_representable (by decide +kernel +revert)
  | ⟨53, _⟩ => iff_of_true Ra54.representable (by decide +kernel +revert)
  | ⟨54, _⟩ => iff_of_true Ra55.representable (by decide +kernel +revert)
  | ⟨55, _⟩ => iff_of_true Ra56.representable (by decide +kernel +revert)
  | ⟨56, _⟩ => iff_of_true Ra57.representable (by decide +kernel +revert)
  | ⟨57, _⟩ => iff_of_false Ra58.not_representable (by decide +kernel +revert)
  | ⟨58, _⟩ => iff_of_false Ra59.not_representable (by decide +kernel +revert)
  | ⟨59, _⟩ => iff_of_false Ra60.not_representable (by decide +kernel +revert)
  | ⟨60, _⟩ => iff_of_true Ra61.representable (by decide +kernel +revert)
  | ⟨61, _⟩ => iff_of_true Ra62.representable (by decide +kernel +revert)
  | ⟨62, _⟩ => iff_of_true Ra63.representable (by decide +kernel +revert)
  | ⟨63, _⟩ => iff_of_true Ra64.representable (by decide +kernel +revert)
  | ⟨64, _⟩ => iff_of_true Ra65.representable (by decide +kernel +revert)
  | ⟨n + 65, h⟩ => False.elim (by omega)

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 65 // Representable (Model idx)} = 45 := by
  let e : {idx : Fin 65 // Representable (Model idx)} ≃
      {idx : Fin 65 // idx ∉ nonrepresentableIndices} :=
    { toFun := fun idx => ⟨idx.val, (model_representable_iff idx.val).mp idx.property⟩
      invFun := fun idx => ⟨idx.val, (model_representable_iff idx.val).mpr idx.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 65 // ¬ Representable (Model idx)} = 20 := by
  let e : {idx : Fin 65 // ¬ Representable (Model idx)} ≃
      {idx : Fin 65 // idx ∈ nonrepresentableIndices} :=
    { toFun := fun idx => ⟨idx.val, by
          simpa only [model_representable_iff, not_not] using idx.property⟩
      invFun := fun idx => ⟨idx.val, by
          simpa only [model_representable_iff, not_not] using idx.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S3N0
