/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1921–1984 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage030

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338510749851389093071714397048327372800
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311043407495591044607987371469675954176
                            83298893461566537105659174552594284544)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13292279957849158729758646543182725120
                            162259276829213363391578010288128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13292442217125987943122038121193013248
                            81129638414606681695789005144064)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14123219855696362189522129507493871616
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14123219855889790320660470175446859776
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          53999887328762207337293622576192421888
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          35390867788255016155983042471979384832
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3489395889610463337466042490223067136
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3489395889610465698649284474801487872
                          256)
                        512)))))
              16384)
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            700376956626096744326928520970240))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)
                          (Code.joinWords 128
                            319845486545321246308087499609478266880
                            338506601457371296883596863966493540352))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            700376956628605501520953019990016))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            10634473003386643836684022794283909120)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633823966279326983230456482242756608
                            128)
                          256)
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          649037107316853453566312041152512
                          10634473003386643836684022794283909120)
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          42535295865117307932921825928971026432
                          53169282093149344208086434539022319616)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986228032036275164608610051293184
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          649037107316853453566312041152512
                          10634635265139353128618174922092445696)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          42535295865117307932921825928971026432
                          53169282100576984443798716188417064960)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          42535295865117307932921825928971026432
                          53169282103052864522369476738215313408)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633823966279326983230456482242756608
                            128)
                          256)
                        (Nat.shiftLeft
                          10675362341147605604837413004993626112
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            10634635265139353128618174922092445696)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986228032036275164608610051293184
                            128)
                          256)
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          649037107316853453566312041152512
                          10634635265139353128618174922092445696)
                        256)))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            822071414248006766870612028686336
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            689601926524156794414206543724544))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            699743131325982629626180169367552
                            128)
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            51339849311752047954640978837504))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          256)
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926524156794414206543724544)
                          256)
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256))
                      1024)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            811296384146066816957890051440640
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            813831685346523275760883457851392
                            128)
                          (Nat.shiftLeft
                            165428403329783936904150221062144
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295875020828247204868128164020224)
                          256)
                        (Nat.shiftLeft
                          42535295865117307935227668938184720384
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295875020828247204868128164020224)
                          256)
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            689601926524156794414206543724544)
                          256)
                        (Nat.shiftLeft
                          42535295865117307935227668938184720384
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256))
                      1024))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298581732775830629071739058787719315456
                            319850029745496599891653538064245981184)
                          (Code.joinWords 128
                            298582381812937945925192625099760467968
                            83299572288462959307765425770149707776))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            781506595040703426022717526114304))
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            21268296969665970819914479276526665728
                            689601926524156794414206543724544))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            699743131325982629626180169367552)
                          (Code.joinWords 128
                            659178312121040472019720489402368
                            51339849311752047954640978837504))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633986225556156196593848060253044736
                            42535295865117307932921825928971026432)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292442217125987942401462180813733888
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10633986225556156196593848060253044736
                          42535295865117307932921825928971026432)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926524156794414206543724544)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292442217125987942401462180813733888
                          256)
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          13293131819052512099195876387357458432
                          689601926524156794414206543724544)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            53169282090673464129515673989224071168
                            42535295875020828247204868128164020224)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            288230376151711744
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13292279957849158729038070602803445760
                            162259276829213363391578010288128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13293131819052512099195876387357458432
                            689601926524156794414206543724544)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          53169282090673464129515673989224071168
                          42535295875020828247204868128164020224)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          53169282090673464129515673989224071168
                          42535295875020828247204868128164020224)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          53169119831396634916152282411213783040
                          256)
                        (Code.joinWords 256
                          42701449364590422417034801811506069504
                          42742987739458701040947601343470632960))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13293131819052512099195876387357458432
                            689601926524156794414206543724544)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658618250846660959171005698570977280
                          256)
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2659307852773185115965419905114701824
                          40564819207303340847894502572032)
                        256))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982163263712584746649524371456
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982163263712584746649524371456
                            128)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649300111724307066811110569394831360
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982163263712584746649524371456
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649300111801678319266446836576026624
                            128)
                          256)
                        512)))))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649224052765665805805742977596784640
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982163263712584746649524371456
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649224052765665806093973353748496384
                            128)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255876389248017427419681112299124293632
                            266551751589319775528850485286363201536)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298577838622704798282137296977776345088
                            62359485340598721402226233243418492928)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649305182404080412487438766601928704
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            265845599156983174594596470111351078912
                            311039351013670314276352329110475767808)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            266551751529743911152653078364428435456
                            62359485271003279835800968294960201728)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649305182326707979728716556207652864
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            77371252743566643332907008
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            86200318187952934493534608687104
                            128)
                          256)
                        512)))))
              16384))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            811296384146066816957890051440640
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            814465510646637390461631809454080
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599954931582254187142200996736794624
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599954931582254187142200996736794624
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          43199920004214567695244970229755805696
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            664624139097259762323144300784779264
                            10141204801825835211973625643008))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        (Nat.shiftLeft
                          665273176204576615776710612825931776
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          665263034999774789905469842181324800
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10775030101939949912721977245696
                            128)
                          256)
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        (Nat.shiftLeft
                          665263034999774789905469842181324800
                          256)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968240363283877671731200
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255876389188596305533982859103966330880
                            128)
                          (Nat.shiftLeft
                            333521996411126117905475448815728197632
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            811296384146066816957890051440640
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            814465510646637390470462262214656
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          43199920004214567697514784441950535680
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            706152372925150468947737068533972992
                            128)
                          256)
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          665273176204576615776710612825931776
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          43199920004214567697550813238969499648
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10775030101939949912721977245696
                            128)
                          256)
                        (Nat.shiftLeft
                          664624139097259762323144300784779264
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        (Nat.shiftLeft
                          665273176204576615776710612825931776
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21599954931504882934686864729555599360))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            172400481631039198603551635931136)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599954931582254187142200996736794624
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21599954931582254187142200996736794624))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          53169119831396634916152282411213783040
                          256)
                        (Nat.shiftLeft
                          53376811705738028021872214816499695616
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        162259276829213363391578010288128
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          10141204801825835211973625643008
                          128)
                        (Code.joinWords 128
                          172400481631039198603551635931136
                          10141204801825835211973625643008))))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            10141204801825835211973625643008)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            162259276829213363391578010288128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21599954931504882934686864729555599360
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            10775030101939949912721977245696)
                          256)
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            308380895022100482513683237985039941632)
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            317571260523604129380451230232715722752))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267729062197068573142608753490657280)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            81129638414606681695789005144064)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            172400481631039198603551635931136)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            162259276829213363391578010288128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            81129638414606681695789005144064)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            706152372925150468947737068533972992)
                          256)
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          53169119831396634916152282411213783040
                          256)
                        (Nat.shiftLeft
                          53709118704684256990098166581569781760
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21599960002184655100059806983549616128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            173034306931153313304299987533824
                            10775030101939949912721977245696)
                          256)
                        (Nat.shiftLeft
                          332469892125729548159380358613172224
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          256)
                        512)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298581742976612201982547907462746341376
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            78314288539512836677777355342971142144
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333526068808003993294679086483646709760
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            830767497559000551703220080628203520
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            830777638763802377538432054253846528
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          256)))))
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14123219855889790319939894235067580416
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          56492189821013667103322472596277035008
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          35390867788448444286400807199553093632
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14123219855889790320660470175446859776
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13458605860473212462779327195104935936
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13458605860473250241711198948359667712
                          128)
                        256))))
                8192)
              16384))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162259276829213363391578010288128
                            5316911983139663491615228241121378304)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162259276829213363391578010288128
                            10141204801825835211973625643008)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            21599954931504882934686864729555599360)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            172400481631039198603551635931136)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            21599954931582254187142200996736794624)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599954931582254187142200996736794624
                            21599954931582254187142200996736794624)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            316356262996809977751106080346722009088
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685053713613466904685032937357312
                            128)
                          (Nat.shiftLeft
                            317571260461707127430053303340060639232
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316993112778078098296924030126522368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267653003161054879378518951298334720
                            5070602400912917605986812821504)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162259276829213363391578010288128
                            5316911983139663491615228241121378304)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            172400481631039198603551635931136
                            10141204801825835211973625643008)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          26584559915698317458076141205606891520
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162259276829213363391578010288128
                            5316911983139663491615228241121378304)
                          256)
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          43199909863009765869373729459111198720
                          45899904229612290147677177118065688576)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128)))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10141204801825835211973625643008
                          172400481631039198603551635931136)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          128)
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          128)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          43199909863009765869373729459111198720
                          51216816212751953639292405359187066880)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          26584641045336732065046067370763747328))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            5316911983139663491615228241121378304)
                          256)
                        (Nat.shiftLeft
                          10675362341147605604837413004993626112
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316993112778078098296924030126522368)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            173034306931153313304299987533824
                            5316922758169765431853371339250335744)
                          256)
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          128)
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          664624139097259762287115503765815296
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          830777638570374246400091386300858368
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          256))))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            311043245236314215380212249977847545856
                            128)
                          (Nat.shiftLeft
                            311043894273421532233665816289888698368
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332311542205980186200126729254374211584
                            128)
                          (Nat.shiftLeft
                            78314777156679490549965924788617609216
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            811296384146066816957890051440640
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            819536113047550308067618622275584
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599954931582254187142200996736794624
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            77371252455336267181195264
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          43199920004214567695208941432736841728
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307935227668938184720384
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            10141204801825835211973625643008)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          831429210978891556312460691748421632
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            5070602402093509226704224124928)
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          664624139097259762287115503765815296
                          256)
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830777638570374246400091386300858368
                          10775030101939949912721977245696)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          831429210978891556312460691748421632
                          256)
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256)))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21268296969665970819914479276526665728
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Nat.shiftLeft
                            811296384146066816966686144462848
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            813831685346523275760883457851392
                            128)
                          (Nat.shiftLeft
                            165428403329783936904150221062144
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          43199920004214567695208941432736841728
                          256)
                        (Nat.shiftLeft
                          42535295865117307935227668938184720384
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          45193751856687139678729440049531715584
                          128)
                        (Code.joinWords 128
                          43199909863009765869373729459111198720
                          45235290241623352525508315787118510080))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            831429210978891556312460691748421632
                            21267647932558653966460912964485513216))
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          43199920004214567695208941432736841728
                          256)
                        (Nat.shiftLeft
                          42535295865117307935227668938184720384
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166163640677916309948187856160686080
                          633825300114114700748351602688)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          166815213086433619860557161608249344
                          256)
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            86200240815519599301775817965568
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162259276829213363391578010288128
                            10141204801825835211973625643008)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            21599954931504882934686864729555599360))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            172400481631039198603551635931136
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            172400481631039198603551635931136)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            86200240816700190926891275780096)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            21599954931582254187142200996736794624))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21599954931582254187142200996736794624
                            77371252455336267181195264))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          53169119831396634916152282411213783040
                          256)
                        (Code.joinWords 256
                          42701449364590422417034801811506069504
                          53376811705738028021872214816499695616))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267653003161054879378518951298334720
                            5070602400912917605986812821504)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            172400481631039198603551635931136
                            10141204801825835211973625643008)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602402093509226704224124928)
                          256)
                        512))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            10141204801825835211973625643008)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          173034306931153313304299987533824
                          10775030101939949912721977245696)
                        256)
                      (Nat.shiftLeft
                        162893102129327478092326361890816
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          45193751856687139678729440049531715584
                          128)
                        (Code.joinWords 128
                          43199909863009765869373729459111198720
                          45899904229612290147677177118065688576))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267729062197068573142608753490657280)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584559915698317458364371581758603264
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            288230376151711744
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            172400481631039198603551635931136)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Code.joinWords 128
                          42535295865117307932921825928971026432
                          45193751856687139678729440049531715584)
                        (Code.joinWords 128
                          43199909872913286183656771658304192512
                          45235290241623352525508315787118510080))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          53169119831396634918458125420427476992)
                        (Code.joinWords 256
                          42701449364590422417034801811506069504
                          42742987739458701040947601343470632960))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          173034306931153313304299987533824
                          633825300114114700748351602688)
                        256)
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1920 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage030
