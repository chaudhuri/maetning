%--------------------------------------------------------------------------
% File     : SYN470+1 : ILTP v1.1.2
% Domain   : Syntactic (Translated)
% Problem  : ALC, N=4, R=1, L=68, K=3, D=1, P=0, Index=095
% Version  : Especial.
% English  : 

% Refs     : [OS95]  Ohlbach & Schmidt (1995), Functional Translation and S
%          : [HS97]  Hustadt & Schmidt (1997), On Evaluating Decision Proce
%          : [Wei97] Weidenbach (1997), Email to G. Sutcliffe
% Source   : [Wei97]
% Names    : alc-4-1-68-3-1-095.dfg [Wei97]

% Status   : Theorem
% Rating   : 0.33 v3.1.0, 0.67 v2.7.0, 0.33 v2.6.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.50 v2.2.0, 0.00 v2.1.0
%
% Status (intuit.) : Open
% Rating (intuit.) : 1.00 v1.0.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :  679 (   0 equality)
%            Maximal formula depth :  103 ( 103 average)
%            Number of connectives :  924 ( 246 ~  ; 378  |; 195  &)
%                                         (   0 <=>; 105 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   37 (  33 propositional; 0-1 arity)
%            Number of functors    :   32 (  32 constant; 0-0 arity)
%            Number of variables   :  105 (   0 singleton; 105 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : These ALC problems have been translated from propositional 
%            multi-modal K logic formulae generated according to the scheme
%            described in [HS97], using the optimized functional translation
%            described in [OS95]. The finite model property holds, the
%            Herbrand Universe is finite, they are decidable (the complexity
%            is PSPACE-complete), resolution + subsumption + condensing is a
%            decision procedure, and the translated formulae belong to the
%            (CNF-translation of the) Bernays-Schoenfinkel class [Wei97].
%--------------------------------------------------------------------------
fof(co1,refute,
    ( ~ ( ( ~ hskp0
          | ( ndr1_0
            & c3_1(a494)
            & ~ c0_1(a494)
            & ~ c2_1(a494) ) )
        & ( ~ hskp1
          | ( ndr1_0
            & c1_1(a495)
            & ~ c0_1(a495)
            & ~ c3_1(a495) ) )
        & ( ~ hskp2
          | ( ndr1_0
            & ~ c1_1(a496)
            & ~ c2_1(a496)
            & ~ c3_1(a496) ) )
        & ( ~ hskp3
          | ( ndr1_0
            & c2_1(a497)
            & ~ c0_1(a497)
            & ~ c1_1(a497) ) )
        & ( ~ hskp4
          | ( ndr1_0
            & c1_1(a498)
            & ~ c0_1(a498)
            & ~ c2_1(a498) ) )
        & ( ~ hskp5
          | ( ndr1_0
            & c0_1(a499)
            & c2_1(a499)
            & ~ c1_1(a499) ) )
        & ( ~ hskp6
          | ( ndr1_0
            & c1_1(a501)
            & c2_1(a501)
            & ~ c3_1(a501) ) )
        & ( ~ hskp7
          | ( ndr1_0
            & ~ c0_1(a502)
            & ~ c1_1(a502)
            & ~ c3_1(a502) ) )
        & ( ~ hskp8
          | ( ndr1_0
            & c2_1(a505)
            & c3_1(a505)
            & ~ c0_1(a505) ) )
        & ( ~ hskp9
          | ( ndr1_0
            & c3_1(a507)
            & ~ c0_1(a507)
            & ~ c1_1(a507) ) )
        & ( ~ hskp10
          | ( ndr1_0
            & c0_1(a509)
            & c3_1(a509)
            & ~ c2_1(a509) ) )
        & ( ~ hskp11
          | ( ndr1_0
            & c0_1(a510)
            & ~ c1_1(a510)
            & ~ c2_1(a510) ) )
        & ( ~ hskp12
          | ( ndr1_0
            & c1_1(a514)
            & c3_1(a514)
            & ~ c2_1(a514) ) )
        & ( ~ hskp13
          | ( ndr1_0
            & c0_1(a520)
            & c2_1(a520)
            & ~ c3_1(a520) ) )
        & ( ~ hskp14
          | ( ndr1_0
            & c2_1(a527)
            & ~ c1_1(a527)
            & ~ c3_1(a527) ) )
        & ( ~ hskp15
          | ( ndr1_0
            & c0_1(a528)
            & c1_1(a528)
            & ~ c3_1(a528) ) )
        & ( ~ hskp16
          | ( ndr1_0
            & c2_1(a530)
            & c3_1(a530)
            & ~ c1_1(a530) ) )
        & ( ~ hskp17
          | ( ndr1_0
            & c3_1(a532)
            & ~ c1_1(a532)
            & ~ c2_1(a532) ) )
        & ( ~ hskp18
          | ( ndr1_0
            & c1_1(a533)
            & c2_1(a533)
            & ~ c0_1(a533) ) )
        & ( ~ hskp19
          | ( ndr1_0
            & c1_1(a534)
            & ~ c2_1(a534)
            & ~ c3_1(a534) ) )
        & ( ~ hskp20
          | ( ndr1_0
            & ~ c0_1(a536)
            & ~ c1_1(a536)
            & ~ c2_1(a536) ) )
        & ( ~ hskp21
          | ( ndr1_0
            & c0_1(a538)
            & ~ c1_1(a538)
            & ~ c3_1(a538) ) )
        & ( ~ hskp22
          | ( ndr1_0
            & c1_1(a540)
            & c3_1(a540)
            & ~ c0_1(a540) ) )
        & ( ~ hskp23
          | ( ndr1_0
            & c0_1(a541)
            & c1_1(a541)
            & ~ c2_1(a541) ) )
        & ( ~ hskp24
          | ( ndr1_0
            & c0_1(a554)
            & ~ c2_1(a554)
            & ~ c3_1(a554) ) )
        & ( ~ hskp25
          | ( ndr1_0
            & c2_1(a558)
            & ~ c0_1(a558)
            & ~ c3_1(a558) ) )
        & ( ~ hskp26
          | ( ndr1_0
            & ~ c0_1(a559)
            & ~ c2_1(a559)
            & ~ c3_1(a559) ) )
        & ( ~ hskp27
          | ( ndr1_0
            & c0_1(a568)
            & c3_1(a568)
            & ~ c1_1(a568) ) )
        & ( ~ hskp28
          | ( ndr1_0
            & c0_1(a500)
            & c2_1(a500)
            & c3_1(a500) ) )
        & ( ~ hskp29
          | ( ndr1_0
            & c0_1(a504)
            & c1_1(a504)
            & c3_1(a504) ) )
        & ( ~ hskp30
          | ( ndr1_0
            & c1_1(a512)
            & c2_1(a512)
            & c3_1(a512) ) )
        & ( ~ hskp31
          | ( ndr1_0
            & c0_1(a522)
            & c1_1(a522)
            & c2_1(a522) ) )
        & ( ! [U] : 
              ( ndr1_0
             => ( c0_1(U)
                | c1_1(U)
                | c2_1(U) ) )
          | ! [V] : 
              ( ndr1_0
             => ( c1_1(V)
                | c3_1(V)
                | ~ c2_1(V) ) )
          | hskp0 )
        & ( ! [W] : 
              ( ndr1_0
             => ( c0_1(W)
                | c1_1(W)
                | c3_1(W) ) )
          | ! [X] : 
              ( ndr1_0
             => ( c0_1(X)
                | c2_1(X)
                | c3_1(X) ) )
          | ! [Y] : 
              ( ndr1_0
             => ( c3_1(Y)
                | ~ c1_1(Y)
                | ~ c2_1(Y) ) ) )
        & ( ! [Z] : 
              ( ndr1_0
             => ( c0_1(Z)
                | c1_1(Z)
                | c3_1(Z) ) )
          | ! [X1] : 
              ( ndr1_0
             => ( c1_1(X1)
                | c3_1(X1)
                | ~ c0_1(X1) ) )
          | hskp1 )
        & ( ! [X2] : 
              ( ndr1_0
             => ( c0_1(X2)
                | c1_1(X2)
                | c3_1(X2) ) )
          | ! [X3] : 
              ( ndr1_0
             => ( ~ c0_1(X3)
                | ~ c1_1(X3)
                | ~ c2_1(X3) ) )
          | hskp2 )
        & ( ! [X4] : 
              ( ndr1_0
             => ( c0_1(X4)
                | c1_1(X4)
                | ~ c2_1(X4) ) )
          | ! [X5] : 
              ( ndr1_0
             => ( c0_1(X5)
                | ~ c2_1(X5)
                | ~ c3_1(X5) ) )
          | hskp3 )
        & ( ! [X6] : 
              ( ndr1_0
             => ( c0_1(X6)
                | c1_1(X6)
                | ~ c2_1(X6) ) )
          | ! [X7] : 
              ( ndr1_0
             => ( c3_1(X7)
                | ~ c0_1(X7)
                | ~ c2_1(X7) ) )
          | hskp4 )
        & ( ! [X8] : 
              ( ndr1_0
             => ( c0_1(X8)
                | c1_1(X8)
                | ~ c2_1(X8) ) )
          | ! [X9] : 
              ( ndr1_0
             => ( ~ c0_1(X9)
                | ~ c1_1(X9)
                | ~ c2_1(X9) ) )
          | hskp5 )
        & ( ! [X10] : 
              ( ndr1_0
             => ( c0_1(X10)
                | c1_1(X10)
                | ~ c2_1(X10) ) )
          | hskp28
          | hskp6 )
        & ( ! [X11] : 
              ( ndr1_0
             => ( c0_1(X11)
                | c1_1(X11)
                | ~ c3_1(X11) ) )
          | ! [X12] : 
              ( ndr1_0
             => ( c0_1(X12)
                | c2_1(X12)
                | ~ c1_1(X12) ) )
          | ! [X13] : 
              ( ndr1_0
             => ( c2_1(X13)
                | ~ c1_1(X13)
                | ~ c3_1(X13) ) ) )
        & ( ! [X14] : 
              ( ndr1_0
             => ( c0_1(X14)
                | c1_1(X14)
                | ~ c3_1(X14) ) )
          | ! [X15] : 
              ( ndr1_0
             => ( c1_1(X15)
                | ~ c0_1(X15)
                | ~ c2_1(X15) ) )
          | hskp7 )
        & ( ! [X16] : 
              ( ndr1_0
             => ( c0_1(X16)
                | c1_1(X16)
                | ~ c3_1(X16) ) )
          | ! [X17] : 
              ( ndr1_0
             => ( c1_1(X17)
                | ~ c0_1(X17)
                | ~ c3_1(X17) ) )
          | hskp28 )
        & ( ! [X18] : 
              ( ndr1_0
             => ( c0_1(X18)
                | c1_1(X18)
                | ~ c3_1(X18) ) )
          | hskp29
          | hskp8 )
        & ( ! [X19] : 
              ( ndr1_0
             => ( c0_1(X19)
                | c1_1(X19)
                | ~ c3_1(X19) ) )
          | hskp6
          | hskp9 )
        & ( ! [X20] : 
              ( ndr1_0
             => ( c0_1(X20)
                | c2_1(X20)
                | c3_1(X20) ) )
          | ! [X21] : 
              ( ndr1_0
             => ( c0_1(X21)
                | ~ c1_1(X21)
                | ~ c2_1(X21) ) )
          | ! [X22] : 
              ( ndr1_0
             => ( ~ c1_1(X22)
                | ~ c2_1(X22)
                | ~ c3_1(X22) ) ) )
        & ( ! [X23] : 
              ( ndr1_0
             => ( c0_1(X23)
                | c2_1(X23)
                | c3_1(X23) ) )
          | ! [X24] : 
              ( ndr1_0
             => ( c2_1(X24)
                | ~ c0_1(X24)
                | ~ c1_1(X24) ) )
          | ! [X25] : 
              ( ndr1_0
             => ( c3_1(X25)
                | ~ c0_1(X25)
                | ~ c1_1(X25) ) ) )
        & ( ! [X26] : 
              ( ndr1_0
             => ( c0_1(X26)
                | c2_1(X26)
                | c3_1(X26) ) )
          | ! [X27] : 
              ( ndr1_0
             => ( c2_1(X27)
                | ~ c0_1(X27)
                | ~ c1_1(X27) ) )
          | hskp6 )
        & ( ! [X28] : 
              ( ndr1_0
             => ( c0_1(X28)
                | c2_1(X28)
                | c3_1(X28) ) )
          | hskp10
          | hskp11 )
        & ( ! [X29] : 
              ( ndr1_0
             => ( c0_1(X29)
                | c2_1(X29)
                | ~ c1_1(X29) ) )
          | ! [X30] : 
              ( ndr1_0
             => ( c0_1(X30)
                | ~ c1_1(X30)
                | ~ c2_1(X30) ) )
          | ! [X31] : 
              ( ndr1_0
             => ( c2_1(X31)
                | ~ c1_1(X31)
                | ~ c3_1(X31) ) ) )
        & ( ! [X32] : 
              ( ndr1_0
             => ( c0_1(X32)
                | c2_1(X32)
                | ~ c1_1(X32) ) )
          | ! [X33] : 
              ( ndr1_0
             => ( c1_1(X33)
                | c2_1(X33)
                | ~ c0_1(X33) ) )
          | hskp9 )
        & ( ! [X34] : 
              ( ndr1_0
             => ( c0_1(X34)
                | c2_1(X34)
                | ~ c1_1(X34) ) )
          | hskp30
          | hskp4 )
        & ( ! [X35] : 
              ( ndr1_0
             => ( c0_1(X35)
                | c2_1(X35)
                | ~ c1_1(X35) ) )
          | hskp12
          | hskp8 )
        & ( ! [X36] : 
              ( ndr1_0
             => ( c0_1(X36)
                | c2_1(X36)
                | ~ c3_1(X36) ) )
          | ! [X37] : 
              ( ndr1_0
             => ( c0_1(X37)
                | c3_1(X37)
                | ~ c1_1(X37) ) )
          | ! [X38] : 
              ( ndr1_0
             => ( c3_1(X38)
                | ~ c0_1(X38)
                | ~ c1_1(X38) ) ) )
        & ( ! [X39] : 
              ( ndr1_0
             => ( c0_1(X39)
                | c3_1(X39)
                | ~ c1_1(X39) ) )
          | ! [X40] : 
              ( ndr1_0
             => ( c1_1(X40)
                | ~ c0_1(X40)
                | ~ c3_1(X40) ) )
          | hskp8 )
        & ( ! [X41] : 
              ( ndr1_0
             => ( c0_1(X41)
                | c3_1(X41)
                | ~ c1_1(X41) ) )
          | hskp1
          | hskp7 )
        & ( ! [X42] : 
              ( ndr1_0
             => ( c0_1(X42)
                | c3_1(X42)
                | ~ c2_1(X42) ) )
          | ! [X43] : 
              ( ndr1_0
             => ( ~ c0_1(X43)
                | ~ c1_1(X43)
                | ~ c2_1(X43) ) )
          | hskp28 )
        & ( ! [X44] : 
              ( ndr1_0
             => ( c0_1(X44)
                | c3_1(X44)
                | ~ c2_1(X44) ) )
          | hskp13
          | hskp30 )
        & ( ! [X45] : 
              ( ndr1_0
             => ( c0_1(X45)
                | ~ c1_1(X45)
                | ~ c2_1(X45) ) )
          | hskp31
          | hskp30 )
        & ( ! [X46] : 
              ( ndr1_0
             => ( c0_1(X46)
                | ~ c1_1(X46)
                | ~ c2_1(X46) ) )
          | hskp31
          | hskp1 )
        & ( ! [X47] : 
              ( ndr1_0
             => ( c0_1(X47)
                | ~ c1_1(X47)
                | ~ c3_1(X47) ) )
          | ! [X48] : 
              ( ndr1_0
             => ( c1_1(X48)
                | c2_1(X48)
                | ~ c0_1(X48) ) )
          | hskp10 )
        & ( ! [X49] : 
              ( ndr1_0
             => ( c0_1(X49)
                | ~ c1_1(X49)
                | ~ c3_1(X49) ) )
          | ! [X50] : 
              ( ndr1_0
             => ( c1_1(X50)
                | ~ c0_1(X50)
                | ~ c3_1(X50) ) )
          | ! [X51] : 
              ( ndr1_0
             => ( c3_1(X51)
                | ~ c0_1(X51)
                | ~ c1_1(X51) ) ) )
        & ( ! [X52] : 
              ( ndr1_0
             => ( c0_1(X52)
                | ~ c2_1(X52)
                | ~ c3_1(X52) ) )
          | ! [X53] : 
              ( ndr1_0
             => ( c1_1(X53)
                | c2_1(X53)
                | ~ c0_1(X53) ) )
          | hskp14 )
        & ( ! [X54] : 
              ( ndr1_0
             => ( c0_1(X54)
                | ~ c2_1(X54)
                | ~ c3_1(X54) ) )
          | ! [X55] : 
              ( ndr1_0
             => ( c2_1(X55)
                | ~ c0_1(X55)
                | ~ c1_1(X55) ) )
          | hskp15 )
        & ( ! [X56] : 
              ( ndr1_0
             => ( c0_1(X56)
                | ~ c2_1(X56)
                | ~ c3_1(X56) ) )
          | hskp28
          | hskp16 )
        & ( ! [X57] : 
              ( ndr1_0
             => ( c0_1(X57)
                | ~ c2_1(X57)
                | ~ c3_1(X57) ) )
          | hskp4
          | hskp17 )
        & ( ! [X58] : 
              ( ndr1_0
             => ( c1_1(X58)
                | c2_1(X58)
                | c3_1(X58) ) )
          | hskp18
          | hskp19 )
        & ( ! [X59] : 
              ( ndr1_0
             => ( c1_1(X59)
                | c2_1(X59)
                | ~ c0_1(X59) ) )
          | ! [X60] : 
              ( ndr1_0
             => ( c1_1(X60)
                | c2_1(X60)
                | ~ c3_1(X60) ) )
          | hskp9 )
        & ( ! [X61] : 
              ( ndr1_0
             => ( c1_1(X61)
                | c2_1(X61)
                | ~ c0_1(X61) ) )
          | ! [X62] : 
              ( ndr1_0
             => ( c1_1(X62)
                | ~ c0_1(X62)
                | ~ c2_1(X62) ) )
          | hskp20 )
        & ( ! [X63] : 
              ( ndr1_0
             => ( c1_1(X63)
                | c2_1(X63)
                | ~ c0_1(X63) ) )
          | ! [X64] : 
              ( ndr1_0
             => ( c3_1(X64)
                | ~ c0_1(X64)
                | ~ c1_1(X64) ) )
          | hskp9 )
        & ( ! [X65] : 
              ( ndr1_0
             => ( c1_1(X65)
                | c2_1(X65)
                | ~ c0_1(X65) ) )
          | ! [X66] : 
              ( ndr1_0
             => ( c3_1(X66)
                | ~ c1_1(X66)
                | ~ c2_1(X66) ) )
          | hskp21 )
        & ( ! [X67] : 
              ( ndr1_0
             => ( c1_1(X67)
                | c2_1(X67)
                | ~ c0_1(X67) ) )
          | ! [X68] : 
              ( ndr1_0
             => ( ~ c0_1(X68)
                | ~ c1_1(X68)
                | ~ c2_1(X68) ) )
          | hskp3 )
        & ( ! [X69] : 
              ( ndr1_0
             => ( c1_1(X69)
                | c3_1(X69)
                | ~ c0_1(X69) ) )
          | ! [X70] : 
              ( ndr1_0
             => ( c2_1(X70)
                | c3_1(X70)
                | ~ c0_1(X70) ) )
          | hskp22 )
        & ( ! [X71] : 
              ( ndr1_0
             => ( c1_1(X71)
                | c3_1(X71)
                | ~ c0_1(X71) ) )
          | ! [X72] : 
              ( ndr1_0
             => ( c3_1(X72)
                | ~ c0_1(X72)
                | ~ c1_1(X72) ) )
          | hskp23 )
        & ( ! [X73] : 
              ( ndr1_0
             => ( c1_1(X73)
                | c3_1(X73)
                | ~ c0_1(X73) ) )
          | hskp31
          | hskp4 )
        & ( ! [X74] : 
              ( ndr1_0
             => ( c1_1(X74)
                | c3_1(X74)
                | ~ c0_1(X74) ) )
          | hskp5
          | hskp7 )
        & ( ! [X75] : 
              ( ndr1_0
             => ( c1_1(X75)
                | c3_1(X75)
                | ~ c2_1(X75) ) )
          | hskp12
          | hskp20 )
        & ( ! [X76] : 
              ( ndr1_0
             => ( c1_1(X76)
                | ~ c0_1(X76)
                | ~ c3_1(X76) ) )
          | ! [X77] : 
              ( ndr1_0
             => ( c1_1(X77)
                | ~ c2_1(X77)
                | ~ c3_1(X77) ) )
          | hskp29 )
        & ( ! [X78] : 
              ( ndr1_0
             => ( c1_1(X78)
                | ~ c2_1(X78)
                | ~ c3_1(X78) ) )
          | ! [X79] : 
              ( ndr1_0
             => ( c2_1(X79)
                | ~ c1_1(X79)
                | ~ c3_1(X79) ) )
          | hskp20 )
        & ( ! [X80] : 
              ( ndr1_0
             => ( c2_1(X80)
                | ~ c0_1(X80)
                | ~ c1_1(X80) ) )
          | ! [X81] : 
              ( ndr1_0
             => ( c2_1(X81)
                | ~ c0_1(X81)
                | ~ c3_1(X81) ) )
          | hskp2 )
        & ( ! [X82] : 
              ( ndr1_0
             => ( c2_1(X82)
                | ~ c0_1(X82)
                | ~ c1_1(X82) ) )
          | ! [X83] : 
              ( ndr1_0
             => ( ~ c1_1(X83)
                | ~ c2_1(X83)
                | ~ c3_1(X83) ) )
          | hskp31 )
        & ( ! [X84] : 
              ( ndr1_0
             => ( c2_1(X84)
                | ~ c0_1(X84)
                | ~ c1_1(X84) ) )
          | hskp5
          | hskp4 )
        & ( ! [X85] : 
              ( ndr1_0
             => ( c2_1(X85)
                | ~ c0_1(X85)
                | ~ c3_1(X85) ) )
          | ! [X86] : 
              ( ndr1_0
             => ( c3_1(X86)
                | ~ c0_1(X86)
                | ~ c2_1(X86) ) )
          | hskp24 )
        & ( ! [X87] : 
              ( ndr1_0
             => ( c2_1(X87)
                | ~ c0_1(X87)
                | ~ c3_1(X87) ) )
          | hskp15
          | hskp10 )
        & ( ! [X88] : 
              ( ndr1_0
             => ( c2_1(X88)
                | ~ c1_1(X88)
                | ~ c3_1(X88) ) )
          | ! [X89] : 
              ( ndr1_0
             => ( c3_1(X89)
                | ~ c0_1(X89)
                | ~ c2_1(X89) ) )
          | hskp17 )
        & ( ! [X90] : 
              ( ndr1_0
             => ( c2_1(X90)
                | ~ c1_1(X90)
                | ~ c3_1(X90) ) )
          | hskp25
          | hskp26 )
        & ( ! [X91] : 
              ( ndr1_0
             => ( c3_1(X91)
                | ~ c0_1(X91)
                | ~ c1_1(X91) ) )
          | ! [X92] : 
              ( ndr1_0
             => ( ~ c0_1(X92)
                | ~ c2_1(X92)
                | ~ c3_1(X92) ) )
          | hskp2 )
        & ( ! [X93] : 
              ( ndr1_0
             => ( c3_1(X93)
                | ~ c0_1(X93)
                | ~ c1_1(X93) ) )
          | hskp16
          | hskp25 )
        & ( ! [X94] : 
              ( ndr1_0
             => ( c3_1(X94)
                | ~ c1_1(X94)
                | ~ c2_1(X94) ) )
          | ! [X95] : 
              ( ndr1_0
             => ( ~ c0_1(X95)
                | ~ c2_1(X95)
                | ~ c3_1(X95) ) )
          | hskp0 )
        & ( ! [X96] : 
              ( ndr1_0
             => ( ~ c0_1(X96)
                | ~ c1_1(X96)
                | ~ c2_1(X96) ) )
          | hskp12
          | hskp8 )
        & ( ! [X97] : 
              ( ndr1_0
             => ( ~ c1_1(X97)
                | ~ c2_1(X97)
                | ~ c3_1(X97) ) )
          | hskp13
          | hskp3 )
        & ( ! [X98] : 
              ( ndr1_0
             => ( ~ c1_1(X98)
                | ~ c2_1(X98)
                | ~ c3_1(X98) ) )
          | hskp27
          | hskp19 )
        & ( ! [X99] : 
              ( ndr1_0
             => ( ~ c1_1(X99)
                | ~ c2_1(X99)
                | ~ c3_1(X99) ) )
          | hskp22
          | hskp17 )
        & ( hskp15
          | hskp13
          | hskp12 )
        & ( hskp28
          | hskp13
          | hskp10 )
        & ( hskp28
          | hskp21
          | hskp20 )
        & ( hskp13
          | hskp6
          | hskp14 )
        & ( hskp27
          | hskp10
          | hskp26 )
        & ( hskp11
          | hskp17
          | hskp26 )
        & ( hskp4
          | hskp8
          | hskp2 ) ) )).

%--------------------------------------------------------------------------