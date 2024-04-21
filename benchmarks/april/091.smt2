(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info
  :source |
 Generated by PSyCO 0.1
 More info in N. P. Lopes and J. Monteiro. Weakest Precondition Synthesis for
 Compiler Optimizations, VMCAI'14.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun R_E1_V4 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun R_E1_V5 () Bool)
(declare-fun W_S1_V5 () Bool)
(declare-fun W_S2_V5 () Bool)
(declare-fun W_S2_V2 () Bool)
(declare-fun W_S2_V3 () Bool)
(declare-fun W_S2_V1 () Bool)
(declare-fun R_S2_V4 () Bool)
(declare-fun R_S2_V5 () Bool)
(declare-fun R_S2_V2 () Bool)
(declare-fun R_S2_V3 () Bool)
(declare-fun R_S2_V1 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V5 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_E1_V2 () Bool)
(declare-fun DISJ_W_S2_R_E1 () Bool)
(declare-fun DISJ_W_S2_R_S2 () Bool)
(declare-fun DISJ_W_S2_R_S1 () Bool)
(declare-fun DISJ_W_S1_W_S2 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun DISJ_W_S1_R_S2 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S2_V4 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_E1_V1 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(assert
 (let
 (($x5110
   (forall
    ((V3_0 (_ BitVec 32)) (V2_0 (_ BitVec 32)) 
     (V5_0 (_ BitVec 32)) (V4_0 (_ BitVec 32)) 
     (MW_S1_V1 Bool) (MW_S1_V3 Bool) 
     (MW_S1_V2 Bool) (MW_S1_V5 Bool) 
     (MW_S1_V4 Bool) (MW_S2_V1 Bool) 
     (MW_S2_V3 Bool) (MW_S2_V2 Bool) 
     (MW_S2_V5 Bool) (MW_S2_V4 Bool) 
     (S1_V1_!6442 (_ BitVec 32)) (S1_V1_!6447 (_ BitVec 32)) 
     (S1_V1_!6464 (_ BitVec 32)) (S1_V1_!6474 (_ BitVec 32)) 
     (S2_V5_!6456 (_ BitVec 32)) (S2_V5_!6461 (_ BitVec 32)) 
     (S2_V5_!6472 (_ BitVec 32)) (S2_V5_!6482 (_ BitVec 32)) 
     (S1_V3_!6443 (_ BitVec 32)) (S1_V3_!6448 (_ BitVec 32)) 
     (S1_V3_!6465 (_ BitVec 32)) (S1_V3_!6475 (_ BitVec 32)) 
     (S1_V2_!6444 (_ BitVec 32)) (S1_V2_!6449 (_ BitVec 32)) 
     (S1_V2_!6466 (_ BitVec 32)) (S1_V2_!6476 (_ BitVec 32)) 
     (E1_!6441 (_ BitVec 32)) (E1_!6452 (_ BitVec 32)) 
     (E1_!6463 (_ BitVec 32)) (S2_V4_!6457 (_ BitVec 32)) 
     (S2_V4_!6462 (_ BitVec 32)) (S2_V4_!6473 (_ BitVec 32)) 
     (S2_V4_!6483 (_ BitVec 32)) (S1_V5_!6445 (_ BitVec 32)) 
     (S1_V5_!6450 (_ BitVec 32)) (S1_V5_!6467 (_ BitVec 32)) 
     (S1_V5_!6477 (_ BitVec 32)) (S2_V1_!6453 (_ BitVec 32)) 
     (S2_V1_!6458 (_ BitVec 32)) (S2_V1_!6469 (_ BitVec 32)) 
     (S2_V1_!6479 (_ BitVec 32)) (S1_V4_!6446 (_ BitVec 32)) 
     (S1_V4_!6451 (_ BitVec 32)) (S1_V4_!6468 (_ BitVec 32)) 
     (S1_V4_!6478 (_ BitVec 32)) (S2_V2_!6455 (_ BitVec 32)) 
     (S2_V2_!6460 (_ BitVec 32)) (S2_V2_!6471 (_ BitVec 32)) 
     (S2_V2_!6481 (_ BitVec 32)) (S2_V3_!6454 (_ BitVec 32)) 
     (S2_V3_!6459 (_ BitVec 32)) (S2_V3_!6470 (_ BitVec 32)) 
     (S2_V3_!6480 (_ BitVec 32)))
    (let
    (($x2611
      (= (ite MW_S2_V4 S2_V4_!6462 (ite MW_S1_V4 S1_V4_!6451 V4_0))
      (ite MW_S2_V4 S2_V4_!6483
      (ite MW_S1_V4 S1_V4_!6478
      (ite MW_S2_V4 S2_V4_!6473 (ite MW_S1_V4 S1_V4_!6468 V4_0)))))))
    (let
    (($x3779
      (= (ite MW_S2_V5 S2_V5_!6461 (ite MW_S1_V5 S1_V5_!6450 V5_0))
      (ite MW_S2_V5 S2_V5_!6482
      (ite MW_S1_V5 S1_V5_!6477
      (ite MW_S2_V5 S2_V5_!6472 (ite MW_S1_V5 S1_V5_!6467 V5_0)))))))
    (let
    (($x3858
      (= (ite MW_S2_V2 S2_V2_!6460 (ite MW_S1_V2 S1_V2_!6449 V2_0))
      (ite MW_S2_V2 S2_V2_!6481
      (ite MW_S1_V2 S1_V2_!6476
      (ite MW_S2_V2 S2_V2_!6471 (ite MW_S1_V2 S1_V2_!6466 V2_0)))))))
    (let
    (($x4130
      (= (ite MW_S2_V3 S2_V3_!6459 (ite MW_S1_V3 S1_V3_!6448 V3_0))
      (ite MW_S2_V3 S2_V3_!6480
      (ite MW_S1_V3 S1_V3_!6475
      (ite MW_S2_V3 S2_V3_!6470 (ite MW_S1_V3 S1_V3_!6465 V3_0)))))))
    (let ((?x3364 (ite MW_S1_V1 S1_V1_!6464 E1_!6463)))
    (let ((?x3808 (ite MW_S2_V1 S2_V1_!6469 ?x3364)))
    (let ((?x3750 (bvadd (_ bv1 32) ?x3808)))
    (let ((?x3590 (ite MW_S1_V1 S1_V1_!6474 ?x3750)))
    (let
    (($x2870
      (= (ite MW_S2_V1 S2_V1_!6458 (bvadd (_ bv1 32) (ite MW_S2_V1 S2_V1_!6453 E1_!6452)))
      (ite MW_S2_V1 S2_V1_!6479 ?x3590))))
    (let
    ((?x3579
      (bvadd (bvneg (_ bv1 32))
      (ite MW_S2_V2 S2_V2_!6481
      (ite MW_S1_V2 S1_V2_!6476
      (ite MW_S2_V2 S2_V2_!6471 (ite MW_S1_V2 S1_V2_!6466 V2_0)))))))
    (let
    (($x3549
      (bvsge
      (ite MW_S2_V1 S2_V1_!6458 (bvadd (_ bv1 32) (ite MW_S2_V1 S2_V1_!6453 E1_!6452)))
      (bvadd (bvneg (_ bv1 32)) (ite MW_S2_V2 S2_V2_!6460 (ite MW_S1_V2 S1_V2_!6449 V2_0))))))
    (let ((?x3574 (ite MW_S2_V1 S2_V1_!6453 E1_!6452)))
    (let ((?x2657 (bvadd (_ bv1 32) ?x3574)))
    (let ((?x3208 (ite MW_S1_V2 S1_V2_!6449 V2_0)))
    (let ((?x3144 (ite MW_S2_V2 S2_V2_!6455 ?x3208)))
    (let
    (($x3485
      (and (not (bvsle V2_0 E1_!6441))
      (not
      (bvsle (ite MW_S1_V2 S1_V2_!6444 V2_0)
      (bvadd (_ bv1 32) (ite MW_S1_V1 S1_V1_!6442 E1_!6441))))
      (bvsge
      (ite MW_S1_V1 S1_V1_!6447 (bvadd (_ bv1 32) (ite MW_S1_V1 S1_V1_!6442 E1_!6441)))
      (bvadd (bvneg (_ bv1 32)) ?x3208)) (not (bvsle ?x3208 E1_!6452)) 
      (not (bvsle ?x3144 ?x2657)) $x3549 
      (not (bvsle V2_0 E1_!6463))
      (not
      (bvsle (ite MW_S2_V2 S2_V2_!6471 (ite MW_S1_V2 S1_V2_!6466 V2_0)) ?x3750))
      (bvsge (ite MW_S2_V1 S2_V1_!6479 ?x3590) ?x3579))))
    (let ((?x2628 (ite MW_S1_V4 S1_V4_!6468 V4_0)))
    (let ((?x2734 (ite MW_S2_V4 S2_V4_!6473 ?x2628)))
    (let ((?x3570 (ite MW_S1_V4 S1_V4_!6478 ?x2734)))
    (let (($x407 (not R_S2_V4)))
    (let ((?x3011 (ite MW_S1_V5 S1_V5_!6467 V5_0)))
    (let ((?x3212 (ite MW_S2_V5 S2_V5_!6472 ?x3011)))
    (let ((?x4195 (ite MW_S1_V5 S1_V5_!6477 ?x3212)))
    (let (($x405 (not R_S2_V5)))
    (let ((?x4224 (ite MW_S1_V2 S1_V2_!6466 V2_0)))
    (let ((?x3664 (ite MW_S2_V2 S2_V2_!6471 ?x4224)))
    (let ((?x2481 (ite MW_S1_V2 S1_V2_!6476 ?x3664)))
    (let (($x403 (not R_S2_V2)))
    (let ((?x3297 (ite MW_S1_V3 S1_V3_!6465 V3_0)))
    (let ((?x4222 (ite MW_S2_V3 S2_V3_!6470 ?x3297)))
    (let ((?x3057 (ite MW_S1_V3 S1_V3_!6475 ?x4222)))
    (let (($x401 (not R_S2_V3)))
    (let
    (($x3787
      (and (or (not R_S2_V1) (= ?x3364 ?x3590)) 
      (or $x401 (= ?x3297 ?x3057)) 
      (or $x403 (= ?x4224 ?x2481)) 
      (or $x405 (= ?x3011 ?x4195)) 
      (or $x407 (= ?x2628 ?x3570)))))
    (let (($x3998 (not $x3787)))
    (let
    (($x3876
      (and (or (not R_S2_V1) (= ?x3364 E1_!6452))
      (or $x401 (= ?x3297 (ite MW_S1_V3 S1_V3_!6448 V3_0)))
      (or $x403 (= ?x4224 ?x3208))
      (or $x405 (= ?x3011 (ite MW_S1_V5 S1_V5_!6450 V5_0)))
      (or $x407 (= ?x2628 (ite MW_S1_V4 S1_V4_!6451 V4_0))))))
    (let (($x2497 (not $x3876)))
    (let
    (($x3048
      (and (or (not R_S2_V1) (= ?x3574 (bvadd (bvneg (_ bv1 32)) ?x3590)))
      (or $x401
      (= (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0)) ?x3057))
      (or $x403 (= ?x3144 ?x2481))
      (or $x405
      (= (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0)) ?x4195))
      (or $x407
      (= (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0)) ?x3570)))))
    (let (($x2506 (not $x3048)))
    (let
    (($x2746
      (and (or (not R_S2_V1) (= ?x3574 (bvadd (bvneg (_ bv1 32)) ?x3364)))
      (or $x401
      (= (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0)) ?x3297))
      (or $x403 (= ?x3144 ?x4224))
      (or $x405
      (= (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0)) ?x3011))
      (or $x407
      (= (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0)) ?x2628)))))
    (let (($x2604 (not $x2746)))
    (let
    (($x3060
      (or $x407
      (= (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0))
      (ite MW_S1_V4 S1_V4_!6451 V4_0)))))
    (let
    (($x2918
      (or $x405
      (= (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0))
      (ite MW_S1_V5 S1_V5_!6450 V5_0)))))
    (let
    (($x2528
      (or $x401
      (= (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0))
      (ite MW_S1_V3 S1_V3_!6448 V3_0)))))
    (let
    (($x2662
      (and (or (not R_S2_V1) (= ?x3574 (bvadd (bvneg (_ bv1 32)) E1_!6452))) $x2528
      (or $x403 (= ?x3144 ?x3208)) $x2918 $x3060)))
    (let (($x3068 (not $x2662)))
    (let
    (($x3738
      (and (or (not R_S2_V1) (= E1_!6452 ?x3590))
      (or $x401 (= (ite MW_S1_V3 S1_V3_!6448 V3_0) ?x3057))
      (or $x403 (= ?x3208 ?x2481))
      (or $x405 (= (ite MW_S1_V5 S1_V5_!6450 V5_0) ?x4195))
      (or $x407 (= (ite MW_S1_V4 S1_V4_!6451 V4_0) ?x3570)))))
    (let
    (($x3406
      (and (or (not R_S2_V1) (= ?x3590 ?x2657))
      (or $x401
      (= ?x3057 (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0))))
      (or $x403 (= ?x2481 ?x3144))
      (or $x405
      (= ?x4195 (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0))))
      (or $x407
      (= ?x3570 (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0)))))))
    (let
    (($x2626
      (and (or (not R_S2_V1) (= ?x3590 E1_!6452))
      (or $x401 (= ?x3057 (ite MW_S1_V3 S1_V3_!6448 V3_0)))
      (or $x403 (= ?x2481 ?x3208))
      (or $x405 (= ?x4195 (ite MW_S1_V5 S1_V5_!6450 V5_0)))
      (or $x407 (= ?x3570 (ite MW_S1_V4 S1_V4_!6451 V4_0))))))
    (let (($x2990 (not $x2626)))
    (let
    (($x2620
      (and (or (not R_S2_V1) (= ?x3364 ?x2657))
      (or $x401
      (= ?x3297 (ite MW_S2_V3 S2_V3_!6454 (ite MW_S1_V3 S1_V3_!6448 V3_0))))
      (or $x403 (= ?x4224 ?x3144))
      (or $x405
      (= ?x3011 (ite MW_S2_V5 S2_V5_!6456 (ite MW_S1_V5 S1_V5_!6450 V5_0))))
      (or $x407
      (= ?x2628 (ite MW_S2_V4 S2_V4_!6457 (ite MW_S1_V4 S1_V4_!6451 V4_0)))))))
    (let
    (($x3591
      (and (or (not R_S1_V1) (= ?x3808 (ite MW_S1_V1 S1_V1_!6442 E1_!6441)))
      (or (not R_S1_V3) (= ?x4222 (ite MW_S1_V3 S1_V3_!6443 V3_0)))
      (or (not R_S1_V2) (= ?x3664 (ite MW_S1_V2 S1_V2_!6444 V2_0)))
      (or (not R_S1_V5) (= ?x3212 (ite MW_S1_V5 S1_V5_!6445 V5_0)))
      (or (not R_S1_V4) (= ?x2734 (ite MW_S1_V4 S1_V4_!6446 V4_0))))))
    (let (($x3252 (not $x3591)))
    (let
    (($x2885
      (and (or (not R_S1_V1) (= E1_!6463 ?x3750))
      (or (not R_S1_V3) (= V3_0 ?x4222)) 
      (or (not R_S1_V2) (= V2_0 ?x3664)) 
      (or (not R_S1_V5) (= V5_0 ?x3212)) 
      (or (not R_S1_V4) (= V4_0 ?x2734)))))
    (let
    (($x2750
      (and
      (or (not R_S1_V1)
      (= E1_!6463 (bvadd (_ bv1 32) (ite MW_S1_V1 S1_V1_!6442 E1_!6441))))
      (or (not R_S1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!6443 V3_0)))
      (or (not R_S1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!6444 V2_0)))
      (or (not R_S1_V5) (= V5_0 (ite MW_S1_V5 S1_V5_!6445 V5_0)))
      (or (not R_S1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!6446 V4_0))))))
    (let
    (($x3734
      (and (or (not R_S1_V1) (= E1_!6441 ?x3750))
      (or (not R_S1_V3) (= V3_0 ?x4222)) 
      (or (not R_S1_V2) (= V2_0 ?x3664)) 
      (or (not R_S1_V5) (= V5_0 ?x3212)) 
      (or (not R_S1_V4) (= V4_0 ?x2734)))))
    (let
    (($x2660
      (and
      (or (not R_S1_V1)
      (= E1_!6441 (bvadd (_ bv1 32) (ite MW_S1_V1 S1_V1_!6442 E1_!6441))))
      (or (not R_S1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!6443 V3_0)))
      (or (not R_S1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!6444 V2_0)))
      (or (not R_S1_V5) (= V5_0 (ite MW_S1_V5 S1_V5_!6445 V5_0)))
      (or (not R_S1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!6446 V4_0))))))
    (let
    (($x2962
      (and (or (not R_S1_V1) (= ?x3808 (bvadd (bvneg (_ bv1 32)) E1_!6463)))
      (or (not R_S1_V3) (= ?x4222 V3_0)) 
      (or (not R_S1_V2) (= ?x3664 V2_0)) 
      (or (not R_S1_V5) (= ?x3212 V5_0)) 
      (or (not R_S1_V4) (= ?x2734 V4_0)))))
    (let (($x2691 (not $x2962)))
    (let
    (($x2783
      (and (or (not R_S1_V1) (= ?x3808 (bvadd (bvneg (_ bv1 32)) E1_!6441)))
      (or (not R_S1_V3) (= ?x4222 V3_0)) 
      (or (not R_S1_V2) (= ?x3664 V2_0)) 
      (or (not R_S1_V5) (= ?x3212 V5_0)) 
      (or (not R_S1_V4) (= ?x2734 V4_0)))))
    (let (($x3147 (not $x2783)))
    (let
    (($x2889
      (and (or (not R_S2_V1) (= ?x3590 ?x3364)) 
      (or $x401 (= ?x3057 ?x3297)) 
      (or $x403 (= ?x2481 ?x4224)) 
      (or $x405 (= ?x4195 ?x3011)) 
      (or $x407 (= ?x3570 ?x2628)))))
    (let
    (($x3299
      (and (or (not R_E1_V2) (= ?x3208 V2_0))
      (or (not R_E1_V5) (= (ite MW_S1_V5 S1_V5_!6450 V5_0) V5_0))
      (or (not R_E1_V4) (= (ite MW_S1_V4 S1_V4_!6451 V4_0) V4_0)))))
    (let
    (($x3139
      (and (or (not R_E1_V2) (= V2_0 ?x3208))
      (or (not R_E1_V5) (= V5_0 (ite MW_S1_V5 S1_V5_!6450 V5_0)))
      (or (not R_E1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!6451 V4_0))))))
    (let
    (($x2787
      (and (or (not R_S1_V1) (= (ite MW_S1_V1 S1_V1_!6442 E1_!6441) ?x3808))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!6443 V3_0) ?x4222))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!6444 V2_0) ?x3664))
      (or (not R_S1_V5) (= (ite MW_S1_V5 S1_V5_!6445 V5_0) ?x3212))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!6446 V4_0) ?x2734)))))
    (let
    (($x3315
      (and
      (or (not R_S1_V1)
      (= (ite MW_S1_V1 S1_V1_!6442 E1_!6441) (bvadd (bvneg (_ bv1 32)) E1_!6463)))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!6443 V3_0) V3_0))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!6444 V2_0) V2_0))
      (or (not R_S1_V5) (= (ite MW_S1_V5 S1_V5_!6445 V5_0) V5_0))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!6446 V4_0) V4_0)))))
    (let (($x2821 (not $x3315)))
    (let
    (($x2925
      (and
      (or (not R_S1_V1)
      (= (ite MW_S1_V1 S1_V1_!6442 E1_!6441) (bvadd (bvneg (_ bv1 32)) E1_!6441)))
      (or (not R_S1_V3) (= (ite MW_S1_V3 S1_V3_!6443 V3_0) V3_0))
      (or (not R_S1_V2) (= (ite MW_S1_V2 S1_V2_!6444 V2_0) V2_0))
      (or (not R_S1_V5) (= (ite MW_S1_V5 S1_V5_!6445 V5_0) V5_0))
      (or (not R_S1_V4) (= (ite MW_S1_V4 S1_V4_!6446 V4_0) V4_0)))))
    (let (($x3327 (not $x2925)))
    (let
    (($x3653
      (and (or (not R_S2_V1) (= E1_!6452 ?x3364))
      (or $x401 (= (ite MW_S1_V3 S1_V3_!6448 V3_0) ?x3297))
      (or $x403 (= ?x3208 ?x4224))
      (or $x405 (= (ite MW_S1_V5 S1_V5_!6450 V5_0) ?x3011))
      (or $x407 (= (ite MW_S1_V4 S1_V4_!6451 V4_0) ?x2628)))))
    (let
    (($x3828
      (and
      (or (not (or (not R_S1_V1) (= E1_!6441 E1_!6463)))
      (= S1_V1_!6442 S1_V1_!6464)) 
      (or $x3327 (= S1_V1_!6447 S1_V1_!6442))
      (or $x2821 (= S1_V1_!6447 S1_V1_!6464))
      (or $x3147 (= S1_V1_!6474 S1_V1_!6442))
      (or $x3252 (= S1_V1_!6474 S1_V1_!6447))
      (or $x2691 (= S1_V1_!6474 S1_V1_!6464))
      (or (not $x3653) (= S2_V5_!6456 S2_V5_!6472))
      (or (not $x3738) (= S2_V5_!6456 S2_V5_!6482))
      (or $x3068 (= S2_V5_!6461 S2_V5_!6456))
      (or $x2604 (= S2_V5_!6461 S2_V5_!6472))
      (or $x2506 (= S2_V5_!6461 S2_V5_!6482))
      (or $x3998 (= S2_V5_!6472 S2_V5_!6482))
      (or (not (or (not R_S1_V1) (= E1_!6441 E1_!6463)))
      (= S1_V3_!6443 S1_V3_!6465))
      (or (not $x3734) (= S1_V3_!6443 S1_V3_!6475))
      (or $x3327 (= S1_V3_!6448 S1_V3_!6443))
      (or $x2821 (= S1_V3_!6448 S1_V3_!6465))
      (or (not $x2787) (= S1_V3_!6448 S1_V3_!6475))
      (or (not $x2885) (= S1_V3_!6465 S1_V3_!6475))
      (or (not (or (not R_S1_V1) (= E1_!6441 E1_!6463)))
      (= S1_V2_!6444 S1_V2_!6466)) 
      (or $x3327 (= S1_V2_!6449 S1_V2_!6444))
      (or $x2821 (= S1_V2_!6449 S1_V2_!6466))
      (or (not $x2787) (= S1_V2_!6449 S1_V2_!6476))
      (or $x3147 (= S1_V2_!6476 S1_V2_!6444))
      (or $x2691 (= S1_V2_!6476 S1_V2_!6466))
      (or (not $x3139) (= E1_!6441 E1_!6452)) 
      (= E1_!6441 E1_!6463) 
      (or (not $x3299) (= E1_!6452 E1_!6463))
      (or $x3068 (= S2_V4_!6462 S2_V4_!6457))
      (or $x2604 (= S2_V4_!6462 S2_V4_!6473))
      (or $x2506 (= S2_V4_!6462 S2_V4_!6483))
      (or $x2497 (= S2_V4_!6473 S2_V4_!6457))
      (or $x2990 (= S2_V4_!6483 S2_V4_!6457))
      (or (not $x2889) (= S2_V4_!6483 S2_V4_!6473))
      (or (not $x2660) (= S1_V5_!6445 S1_V5_!6450))
      (or (not (or (not R_S1_V1) (= E1_!6463 E1_!6441)))
      (= S1_V5_!6467 S1_V5_!6445))
      (or (not $x2750) (= S1_V5_!6467 S1_V5_!6450))
      (or $x3147 (= S1_V5_!6477 S1_V5_!6445))
      (or $x3252 (= S1_V5_!6477 S1_V5_!6450))
      (or $x2691 (= S1_V5_!6477 S1_V5_!6467))
      (or $x3068 (= S2_V1_!6458 S2_V1_!6453))
      (or $x2604 (= S2_V1_!6458 S2_V1_!6469))
      (or $x2506 (= S2_V1_!6458 S2_V1_!6479))
      (or $x2497 (= S2_V1_!6469 S2_V1_!6453))
      (or $x3998 (= S2_V1_!6469 S2_V1_!6479))
      (or $x2990 (= S2_V1_!6479 S2_V1_!6453))
      (or (not $x2660) (= S1_V4_!6446 S1_V4_!6451))
      (or (not $x3734) (= S1_V4_!6446 S1_V4_!6478))
      (or (not (or (not R_S1_V1) (= E1_!6463 E1_!6441)))
      (= S1_V4_!6468 S1_V4_!6446))
      (or (not $x2750) (= S1_V4_!6468 S1_V4_!6451))
      (or (not $x2885) (= S1_V4_!6468 S1_V4_!6478))
      (or $x3252 (= S1_V4_!6478 S1_V4_!6451))
      (or $x3068 (= S2_V2_!6460 S2_V2_!6455))
      (or $x2497 (= S2_V2_!6471 S2_V2_!6455))
      (or (not $x2620) (= S2_V2_!6471 S2_V2_!6460))
      (or $x3998 (= S2_V2_!6471 S2_V2_!6481))
      (or $x2990 (= S2_V2_!6481 S2_V2_!6455))
      (or (not $x3406) (= S2_V2_!6481 S2_V2_!6460))
      (or (not $x3738) (= S2_V3_!6454 S2_V3_!6480))
      (or $x3068 (= S2_V3_!6459 S2_V3_!6454))
      (or $x2604 (= S2_V3_!6459 S2_V3_!6470))
      (or $x2506 (= S2_V3_!6459 S2_V3_!6480))
      (or $x2497 (= S2_V3_!6470 S2_V3_!6454))
      (or $x3998 (= S2_V3_!6470 S2_V3_!6480)) 
      (not MW_S1_V1) (not MW_S1_V2) 
      (or (not MW_S1_V5) W_S1_V5) 
      (or (not MW_S1_V4) W_S1_V4) 
      (or (not MW_S2_V1) W_S2_V1) 
      (or (not MW_S2_V3) W_S2_V3) 
      (or (not MW_S2_V2) W_S2_V2) 
      (or (not MW_S2_V5) W_S2_V5))))
    (or (not $x3828) (not $x3485) (and $x2870 $x4130 $x3858 $x3779 $x2611)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let
 (($x3325 (not (or (and W_S2_V2 R_E1_V2) (and W_S2_V5 R_E1_V5) R_E1_V4))))
 (let
 (($x113
   (or (and W_S2_V1 R_S2_V1) 
   (and W_S2_V3 R_S2_V3) (and W_S2_V2 R_S2_V2) 
   (and W_S2_V5 R_S2_V5) R_S2_V4)))
 (let (($x115 (= DISJ_W_S2_R_S2 (not $x113))))
 (let
 (($x110
   (or (and W_S2_V1 R_S1_V1) 
   (and W_S2_V3 R_S1_V3) (and W_S2_V2 R_S1_V2) 
   (and W_S2_V5 R_S1_V5) R_S1_V4)))
 (let (($x112 (= DISJ_W_S2_R_S1 (not $x110))))
 (let
 (($x3897
   (= DISJ_W_S1_W_S2 (not (or W_S2_V3 (and W_S1_V5 W_S2_V5) W_S1_V4)))))
 (let (($x155 (not R_E1_V3)))
 (let
 (($x3855 (not (or R_S2_V3 (and W_S1_V5 R_S2_V5) (and W_S1_V4 R_S2_V4)))))
 (let
 (($x2785 (not (or R_S1_V3 (and W_S1_V5 R_S1_V5) (and W_S1_V4 R_S1_V4)))))
 (let (($x2398 (not W_S2_V3)))
 (let (($x2387 (not W_S2_V2)))
 (let (($x407 (not R_S2_V4)))
 (let (($x398 (not R_S2_V1)))
 (let
 (($x6996
   (or (and DISJ_W_S2_R_S1 DISJ_W_S2_R_S2) 
   (and $x2387 DISJ_W_S2_R_S2) 
   (and DISJ_W_S1_R_S2 DISJ_W_S2_R_S1)
   (and (not R_S2_V3) (not W_S1_V4) (not W_S2_V5) DISJ_W_S2_R_S1)
   (and $x407 (not W_S2_V5) $x2398 DISJ_W_S2_R_S1)
   (and (not R_S2_V3) $x407 (not W_S2_V5) DISJ_W_S2_R_S1)
   (and (not W_S2_V1) $x2387)
   (and $x398 (not R_S2_V3) $x2387 (not W_S2_V5) DISJ_W_S2_R_S1)
   (and $x398 (not R_S2_V5) $x407 $x2387 DISJ_W_S2_R_S1)
   (and $x398 $x407 $x2387 (not W_S2_V5) DISJ_W_S2_R_S1)
   (and $x398 (not R_S2_V3) $x407 $x2387 DISJ_W_S2_R_S1)
   (and $x398 (not R_S2_V3) (not R_S2_V5) $x2387 DISJ_W_S2_R_S1)
   (and DISJ_W_S1_W_S2 DISJ_W_S2_R_S1)
   (and $x398 $x2387 (not W_S2_V5) $x2398 DISJ_W_S2_R_S1)
   (and (not R_S2_V5) (not W_S1_V4) $x2398 DISJ_W_S2_R_S1)
   (and $x398 (not R_S2_V5) $x2387 $x2398 DISJ_W_S2_R_S1)
   (and $x407 (not W_S1_V5) $x2398 DISJ_W_S2_R_S1)
   (and (not R_S2_V5) $x407 $x2398 DISJ_W_S2_R_S1)
   (and $x398 $x407 $x2387 $x2398 DISJ_W_S2_R_S1))))
 (let
 (($x3290
   (or (and $x2387 DISJ_W_S2_R_S1 DISJ_W_S1_R_S1) 
   (and (not W_S2_V1) $x2387) 
   (and (not R_S1_V1) DISJ_W_S1_R_S1))))
 (let (($x2350 (not W_S1_V2)))
 (let (($x2301 (not W_S1_V1)))
 (let (($x153 (not R_E1_V1)))
 (and DISJ_W_S1_R_E1 $x153 $x2301 $x2350 $x3290 $x6996 W_S1_V3 W_S2_V4
 (= DISJ_W_S1_R_S1 $x2785) 
 (= DISJ_W_S1_R_S2 $x3855) $x155 $x3897 $x112 $x115 
 (= DISJ_W_S2_R_E1 $x3325) $x5110 
 (not (and W_S1_V5 R_E1_V5)) 
 (not (and W_S1_V4 R_E1_V4)))))))))))))))))))))))
(check-sat)
(exit)

