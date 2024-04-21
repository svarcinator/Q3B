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
 (let (($x51 (and W_S1_V4 R_E1_V4)))
 (let (($x3205 (not $x51)))
 (let (($x49 (and W_S1_V5 R_E1_V5)))
 (let (($x2486 (not $x49)))
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
    (let ((?x2628 (ite MW_S1_V4 S1_V4_!6468 V4_0)))
    (let ((?x2734 (ite MW_S2_V4 S2_V4_!6473 ?x2628)))
    (let ((?x3570 (ite MW_S1_V4 S1_V4_!6478 ?x2734)))
    (let ((?x4171 (ite MW_S2_V4 S2_V4_!6483 ?x3570)))
    (let ((?x2725 (ite MW_S1_V4 S1_V4_!6451 V4_0)))
    (let ((?x3468 (ite MW_S2_V4 S2_V4_!6462 ?x2725)))
    (let (($x2611 (= ?x3468 ?x4171)))
    (let ((?x3011 (ite MW_S1_V5 S1_V5_!6467 V5_0)))
    (let ((?x3212 (ite MW_S2_V5 S2_V5_!6472 ?x3011)))
    (let ((?x4195 (ite MW_S1_V5 S1_V5_!6477 ?x3212)))
    (let ((?x2651 (ite MW_S2_V5 S2_V5_!6482 ?x4195)))
    (let ((?x2773 (ite MW_S1_V5 S1_V5_!6450 V5_0)))
    (let ((?x4005 (ite MW_S2_V5 S2_V5_!6461 ?x2773)))
    (let (($x3779 (= ?x4005 ?x2651)))
    (let ((?x4224 (ite MW_S1_V2 S1_V2_!6466 V2_0)))
    (let ((?x3664 (ite MW_S2_V2 S2_V2_!6471 ?x4224)))
    (let ((?x2481 (ite MW_S1_V2 S1_V2_!6476 ?x3664)))
    (let ((?x3727 (ite MW_S2_V2 S2_V2_!6481 ?x2481)))
    (let ((?x3208 (ite MW_S1_V2 S1_V2_!6449 V2_0)))
    (let ((?x4184 (ite MW_S2_V2 S2_V2_!6460 ?x3208)))
    (let (($x3858 (= ?x4184 ?x3727)))
    (let ((?x3297 (ite MW_S1_V3 S1_V3_!6465 V3_0)))
    (let ((?x4222 (ite MW_S2_V3 S2_V3_!6470 ?x3297)))
    (let ((?x3057 (ite MW_S1_V3 S1_V3_!6475 ?x4222)))
    (let ((?x4221 (ite MW_S2_V3 S2_V3_!6480 ?x3057)))
    (let ((?x4155 (ite MW_S1_V3 S1_V3_!6448 V3_0)))
    (let ((?x3857 (ite MW_S2_V3 S2_V3_!6459 ?x4155)))
    (let (($x4130 (= ?x3857 ?x4221)))
    (let ((?x3364 (ite MW_S1_V1 S1_V1_!6464 E1_!6463)))
    (let ((?x3808 (ite MW_S2_V1 S2_V1_!6469 ?x3364)))
    (let ((?x3750 (bvadd (_ bv1 32) ?x3808)))
    (let ((?x3590 (ite MW_S1_V1 S1_V1_!6474 ?x3750)))
    (let ((?x2995 (ite MW_S2_V1 S2_V1_!6479 ?x3590)))
    (let ((?x3574 (ite MW_S2_V1 S2_V1_!6453 E1_!6452)))
    (let ((?x2657 (bvadd (_ bv1 32) ?x3574)))
    (let ((?x3058 (ite MW_S2_V1 S2_V1_!6458 ?x2657)))
    (let (($x2870 (= ?x3058 ?x2995)))
    (let (($x2652 (and $x2870 $x4130 $x3858 $x3779 $x2611)))
    (let ((?x3579 (bvadd (bvneg (_ bv1 32)) ?x3727)))
    (let (($x4141 (bvsge ?x2995 ?x3579)))
    (let (($x4062 (bvsle ?x3664 ?x3750)))
    (let (($x2762 (not $x4062)))
    (let (($x2756 (bvsle V2_0 E1_!6463)))
    (let (($x4107 (not $x2756)))
    (let ((?x3881 (bvadd (bvneg (_ bv1 32)) ?x4184)))
    (let (($x3549 (bvsge ?x3058 ?x3881)))
    (let ((?x3144 (ite MW_S2_V2 S2_V2_!6455 ?x3208)))
    (let (($x2926 (bvsle ?x3144 ?x2657)))
    (let (($x3473 (not $x2926)))
    (let (($x3911 (bvsle ?x3208 E1_!6452)))
    (let (($x4059 (not $x3911)))
    (let ((?x4022 (bvadd (bvneg (_ bv1 32)) ?x3208)))
    (let ((?x4025 (ite MW_S1_V1 S1_V1_!6442 E1_!6441)))
    (let ((?x3584 (bvadd (_ bv1 32) ?x4025)))
    (let ((?x3764 (ite MW_S1_V1 S1_V1_!6447 ?x3584)))
    (let (($x2813 (bvsge ?x3764 ?x4022)))
    (let ((?x2952 (ite MW_S1_V2 S1_V2_!6444 V2_0)))
    (let (($x3677 (bvsle ?x2952 ?x3584)))
    (let (($x4108 (not $x3677)))
    (let (($x3580 (bvsle V2_0 E1_!6441)))
    (let (($x2973 (not $x3580)))
    (let
    (($x3485
      (and $x2973 $x4108 $x2813 $x4059 $x3473 $x3549 $x4107 $x2762 $x4141)))
    (let (($x2446 (not $x3485)))
    (let (($x3596 (not MW_S2_V5)))
    (let (($x3236 (or $x3596 W_S2_V5)))
    (let (($x3844 (not MW_S2_V2)))
    (let (($x3809 (or $x3844 W_S2_V2)))
    (let (($x2583 (not MW_S2_V3)))
    (let (($x3261 (or $x2583 W_S2_V3)))
    (let (($x2649 (not MW_S2_V1)))
    (let (($x2820 (or $x2649 W_S2_V1)))
    (let (($x2718 (not MW_S1_V4)))
    (let (($x2511 (or $x2718 W_S1_V4)))
    (let (($x3550 (not MW_S1_V5)))
    (let (($x3174 (or $x3550 W_S1_V5)))
    (let (($x2948 (not MW_S1_V2)))
    (let (($x2529 (not MW_S1_V1)))
    (let (($x3229 (= S2_V3_!6470 S2_V3_!6480)))
    (let (($x3064 (= ?x2628 ?x3570)))
    (let (($x407 (not R_S2_V4)))
    (let (($x2789 (or $x407 $x3064)))
    (let (($x2967 (= ?x3011 ?x4195)))
    (let (($x405 (not R_S2_V5)))
    (let (($x2811 (or $x405 $x2967)))
    (let (($x2836 (= ?x4224 ?x2481)))
    (let (($x403 (not R_S2_V2)))
    (let (($x2572 (or $x403 $x2836)))
    (let (($x2621 (= ?x3297 ?x3057)))
    (let (($x401 (not R_S2_V3)))
    (let (($x2708 (or $x401 $x2621)))
    (let (($x4032 (= ?x3364 ?x3590)))
    (let (($x398 (not R_S2_V1)))
    (let (($x3165 (or $x398 $x4032)))
    (let (($x3787 (and $x3165 $x2708 $x2572 $x2811 $x2789)))
    (let (($x3998 (not $x3787)))
    (let (($x2921 (or $x3998 $x3229)))
    (let (($x4031 (= S2_V3_!6470 S2_V3_!6454)))
    (let (($x2594 (= ?x2628 ?x2725)))
    (let (($x2480 (or $x407 $x2594)))
    (let (($x3055 (= ?x3011 ?x2773)))
    (let (($x2712 (or $x405 $x3055)))
    (let (($x2606 (= ?x4224 ?x3208)))
    (let (($x2665 (or $x403 $x2606)))
    (let (($x3003 (= ?x3297 ?x4155)))
    (let (($x2869 (or $x401 $x3003)))
    (let (($x3410 (= ?x3364 E1_!6452)))
    (let (($x3527 (or $x398 $x3410)))
    (let (($x3876 (and $x3527 $x2869 $x2665 $x2712 $x2480)))
    (let (($x2497 (not $x3876)))
    (let (($x3537 (or $x2497 $x4031)))
    (let (($x2988 (= S2_V3_!6459 S2_V3_!6480)))
    (let ((?x3093 (ite MW_S2_V4 S2_V4_!6457 ?x2725)))
    (let (($x3130 (= ?x3093 ?x3570)))
    (let (($x3317 (or $x407 $x3130)))
    (let ((?x3708 (ite MW_S2_V5 S2_V5_!6456 ?x2773)))
    (let (($x4084 (= ?x3708 ?x4195)))
    (let (($x4001 (or $x405 $x4084)))
    (let (($x2457 (= ?x3144 ?x2481)))
    (let (($x2730 (or $x403 $x2457)))
    (let ((?x3763 (ite MW_S2_V3 S2_V3_!6454 ?x4155)))
    (let (($x3063 (= ?x3763 ?x3057)))
    (let (($x2688 (or $x401 $x3063)))
    (let ((?x3274 (bvadd (bvneg (_ bv1 32)) ?x3590)))
    (let (($x2727 (= ?x3574 ?x3274)))
    (let (($x2648 (or $x398 $x2727)))
    (let (($x3048 (and $x2648 $x2688 $x2730 $x4001 $x3317)))
    (let (($x2506 (not $x3048)))
    (let (($x3237 (or $x2506 $x2988)))
    (let (($x3427 (= S2_V3_!6459 S2_V3_!6470)))
    (let (($x3383 (= ?x3093 ?x2628)))
    (let (($x2646 (or $x407 $x3383)))
    (let (($x3357 (= ?x3708 ?x3011)))
    (let (($x2565 (or $x405 $x3357)))
    (let (($x2793 (= ?x3144 ?x4224)))
    (let (($x3444 (or $x403 $x2793)))
    (let (($x3680 (= ?x3763 ?x3297)))
    (let (($x3676 (or $x401 $x3680)))
    (let ((?x3450 (bvadd (bvneg (_ bv1 32)) ?x3364)))
    (let (($x3134 (= ?x3574 ?x3450)))
    (let (($x2587 (or $x398 $x3134)))
    (let (($x2746 (and $x2587 $x3676 $x3444 $x2565 $x2646)))
    (let (($x2604 (not $x2746)))
    (let (($x3365 (or $x2604 $x3427)))
    (let (($x2451 (= S2_V3_!6459 S2_V3_!6454)))
    (let (($x2696 (= ?x3093 ?x2725)))
    (let (($x3060 (or $x407 $x2696)))
    (let (($x3634 (= ?x3708 ?x2773)))
    (let (($x2918 (or $x405 $x3634)))
    (let (($x2470 (= ?x3144 ?x3208)))
    (let (($x3009 (or $x403 $x2470)))
    (let (($x3761 (= ?x3763 ?x4155)))
    (let (($x2528 (or $x401 $x3761)))
    (let ((?x2819 (bvadd (bvneg (_ bv1 32)) E1_!6452)))
    (let (($x2716 (= ?x3574 ?x2819)))
    (let (($x3254 (or $x398 $x2716)))
    (let (($x2662 (and $x3254 $x2528 $x3009 $x2918 $x3060)))
    (let (($x3068 (not $x2662)))
    (let (($x3716 (or $x3068 $x2451)))
    (let (($x3348 (= S2_V3_!6454 S2_V3_!6480)))
    (let (($x2677 (= ?x2725 ?x3570)))
    (let (($x2526 (or $x407 $x2677)))
    (let (($x2544 (= ?x2773 ?x4195)))
    (let (($x2950 (or $x405 $x2544)))
    (let (($x3350 (= ?x3208 ?x2481)))
    (let (($x2592 (or $x403 $x3350)))
    (let (($x3250 (= ?x4155 ?x3057)))
    (let (($x3267 (or $x401 $x3250)))
    (let (($x3475 (= E1_!6452 ?x3590)))
    (let (($x3177 (or $x398 $x3475)))
    (let (($x3738 (and $x3177 $x3267 $x2592 $x2950 $x2526)))
    (let (($x3245 (not $x3738)))
    (let (($x2861 (or $x3245 $x3348)))
    (let (($x2722 (= S2_V2_!6481 S2_V2_!6460)))
    (let (($x2961 (= ?x3570 ?x3093)))
    (let (($x4063 (or $x407 $x2961)))
    (let (($x2666 (= ?x4195 ?x3708)))
    (let (($x3032 (or $x405 $x2666)))
    (let (($x2485 (= ?x2481 ?x3144)))
    (let (($x3023 (or $x403 $x2485)))
    (let (($x2291 (= ?x3057 ?x3763)))
    (let (($x2834 (or $x401 $x2291)))
    (let (($x2735 (= ?x3590 ?x2657)))
    (let (($x3746 (or $x398 $x2735)))
    (let (($x3406 (and $x3746 $x2834 $x3023 $x3032 $x4063)))
    (let (($x3503 (not $x3406)))
    (let (($x2473 (or $x3503 $x2722)))
    (let (($x2640 (= S2_V2_!6481 S2_V2_!6455)))
    (let (($x2676 (= ?x3570 ?x2725)))
    (let (($x3109 (or $x407 $x2676)))
    (let (($x2832 (= ?x4195 ?x2773)))
    (let (($x2871 (or $x405 $x2832)))
    (let (($x3534 (= ?x2481 ?x3208)))
    (let (($x2683 (or $x403 $x3534)))
    (let (($x2719 (= ?x3057 ?x4155)))
    (let (($x2875 (or $x401 $x2719)))
    (let (($x2996 (= ?x3590 E1_!6452)))
    (let (($x2695 (or $x398 $x2996)))
    (let (($x2626 (and $x2695 $x2875 $x2683 $x2871 $x3109)))
    (let (($x2990 (not $x2626)))
    (let (($x3774 (or $x2990 $x2640)))
    (let (($x3372 (= S2_V2_!6471 S2_V2_!6481)))
    (let (($x2909 (or $x3998 $x3372)))
    (let (($x3097 (= S2_V2_!6471 S2_V2_!6460)))
    (let (($x3860 (= ?x2628 ?x3093)))
    (let (($x3343 (or $x407 $x3860)))
    (let (($x2766 (= ?x3011 ?x3708)))
    (let (($x3456 (or $x405 $x2766)))
    (let (($x3482 (= ?x4224 ?x3144)))
    (let (($x2910 (or $x403 $x3482)))
    (let (($x2847 (= ?x3297 ?x3763)))
    (let (($x2607 (or $x401 $x2847)))
    (let (($x3370 (= ?x3364 ?x2657)))
    (let (($x2533 (or $x398 $x3370)))
    (let (($x2620 (and $x2533 $x2607 $x2910 $x3456 $x3343)))
    (let (($x3726 (not $x2620)))
    (let (($x2946 (or $x3726 $x3097)))
    (let (($x2670 (= S2_V2_!6471 S2_V2_!6455)))
    (let (($x2644 (or $x2497 $x2670)))
    (let (($x3851 (= S2_V2_!6460 S2_V2_!6455)))
    (let (($x3610 (or $x3068 $x3851)))
    (let (($x4017 (= S1_V4_!6478 S1_V4_!6451)))
    (let ((?x2838 (ite MW_S1_V4 S1_V4_!6446 V4_0)))
    (let (($x3051 (= ?x2734 ?x2838)))
    (let (($x206 (not R_S1_V4)))
    (let (($x2709 (or $x206 $x3051)))
    (let ((?x2792 (ite MW_S1_V5 S1_V5_!6445 V5_0)))
    (let (($x2940 (= ?x3212 ?x2792)))
    (let (($x204 (not R_S1_V5)))
    (let (($x2856 (or $x204 $x2940)))
    (let (($x3079 (= ?x3664 ?x2952)))
    (let (($x202 (not R_S1_V2)))
    (let (($x2650 (or $x202 $x3079)))
    (let ((?x3193 (ite MW_S1_V3 S1_V3_!6443 V3_0)))
    (let (($x3328 (= ?x4222 ?x3193)))
    (let (($x200 (not R_S1_V3)))
    (let (($x2556 (or $x200 $x3328)))
    (let (($x3909 (= ?x3808 ?x4025)))
    (let (($x198 (not R_S1_V1)))
    (let (($x3467 (or $x198 $x3909)))
    (let (($x3591 (and $x3467 $x2556 $x2650 $x2856 $x2709)))
    (let (($x3252 (not $x3591)))
    (let (($x2464 (or $x3252 $x4017)))
    (let (($x3378 (= S1_V4_!6468 S1_V4_!6478)))
    (let (($x3054 (= V4_0 ?x2734)))
    (let (($x2831 (or $x206 $x3054)))
    (let (($x3272 (= V5_0 ?x3212)))
    (let (($x2748 (or $x204 $x3272)))
    (let (($x2524 (= V2_0 ?x3664)))
    (let (($x2913 (or $x202 $x2524)))
    (let (($x3987 (= V3_0 ?x4222)))
    (let (($x3392 (or $x200 $x3987)))
    (let (($x2980 (= E1_!6463 ?x3750)))
    (let (($x2852 (or $x198 $x2980)))
    (let (($x2885 (and $x2852 $x3392 $x2913 $x2748 $x2831)))
    (let (($x2800 (not $x2885)))
    (let (($x3094 (or $x2800 $x3378)))
    (let (($x2720 (= S1_V4_!6468 S1_V4_!6451)))
    (let (($x2920 (= V4_0 ?x2838)))
    (let (($x3213 (or $x206 $x2920)))
    (let (($x3059 (= V5_0 ?x2792)))
    (let (($x2976 (or $x204 $x3059)))
    (let (($x2848 (= V2_0 ?x2952)))
    (let (($x2702 (or $x202 $x2848)))
    (let (($x3163 (= V3_0 ?x3193)))
    (let (($x2934 (or $x200 $x3163)))
    (let (($x3158 (= E1_!6463 ?x3584)))
    (let (($x3185 (or $x198 $x3158)))
    (let (($x2750 (and $x3185 $x2934 $x2702 $x2976 $x3213)))
    (let (($x2671 (not $x2750)))
    (let (($x3243 (or $x2671 $x2720)))
    (let (($x3226 (= S1_V4_!6468 S1_V4_!6446)))
    (let (($x3608 (= E1_!6463 E1_!6441)))
    (let (($x3539 (or $x198 $x3608)))
    (let (($x3557 (not $x3539)))
    (let (($x3455 (or $x3557 $x3226)))
    (let (($x3906 (= S1_V4_!6446 S1_V4_!6478)))
    (let (($x3084 (= E1_!6441 ?x3750)))
    (let (($x3221 (or $x198 $x3084)))
    (let (($x3734 (and $x3221 $x3392 $x2913 $x2748 $x2831)))
    (let (($x3705 (not $x3734)))
    (let (($x2729 (or $x3705 $x3906)))
    (let (($x2507 (= S1_V4_!6446 S1_V4_!6451)))
    (let (($x2723 (= E1_!6441 ?x3584)))
    (let (($x2711 (or $x198 $x2723)))
    (let (($x2660 (and $x2711 $x2934 $x2702 $x2976 $x3213)))
    (let (($x2795 (not $x2660)))
    (let (($x2499 (or $x2795 $x2507)))
    (let (($x3266 (= S2_V1_!6479 S2_V1_!6453)))
    (let (($x2761 (or $x2990 $x3266)))
    (let (($x3269 (= S2_V1_!6469 S2_V1_!6479)))
    (let (($x3639 (or $x3998 $x3269)))
    (let (($x3913 (= S2_V1_!6469 S2_V1_!6453)))
    (let (($x2642 (or $x2497 $x3913)))
    (let (($x2812 (= S2_V1_!6458 S2_V1_!6479)))
    (let (($x2440 (or $x2506 $x2812)))
    (let (($x3007 (= S2_V1_!6458 S2_V1_!6469)))
    (let (($x3472 (or $x2604 $x3007)))
    (let (($x2744 (= S2_V1_!6458 S2_V1_!6453)))
    (let (($x2858 (or $x3068 $x2744)))
    (let (($x2431 (= S1_V5_!6477 S1_V5_!6467)))
    (let (($x3065 (= ?x2734 V4_0)))
    (let (($x3682 (or $x206 $x3065)))
    (let (($x2892 (= ?x3212 V5_0)))
    (let (($x3396 (or $x204 $x2892)))
    (let (($x2788 (= ?x3664 V2_0)))
    (let (($x3401 (or $x202 $x2788)))
    (let (($x3149 (= ?x4222 V3_0)))
    (let (($x3321 (or $x200 $x3149)))
    (let ((?x2468 (bvadd (bvneg (_ bv1 32)) E1_!6463)))
    (let (($x2463 (= ?x3808 ?x2468)))
    (let (($x2617 (or $x198 $x2463)))
    (let (($x2962 (and $x2617 $x3321 $x3401 $x3396 $x3682)))
    (let (($x2691 (not $x2962)))
    (let (($x2483 (or $x2691 $x2431)))
    (let (($x3891 (= S1_V5_!6477 S1_V5_!6450)))
    (let (($x2445 (or $x3252 $x3891)))
    (let (($x3380 (= S1_V5_!6477 S1_V5_!6445)))
    (let ((?x2768 (bvadd (bvneg (_ bv1 32)) E1_!6441)))
    (let (($x2630 (= ?x3808 ?x2768)))
    (let (($x3021 (or $x198 $x2630)))
    (let (($x2783 (and $x3021 $x3321 $x3401 $x3396 $x3682)))
    (let (($x3147 (not $x2783)))
    (let (($x3090 (or $x3147 $x3380)))
    (let (($x3389 (= S1_V5_!6467 S1_V5_!6450)))
    (let (($x3645 (or $x2671 $x3389)))
    (let (($x3342 (= S1_V5_!6467 S1_V5_!6445)))
    (let (($x3454 (or $x3557 $x3342)))
    (let (($x2749 (= S1_V5_!6445 S1_V5_!6450)))
    (let (($x3895 (or $x2795 $x2749)))
    (let (($x2603 (= S2_V4_!6483 S2_V4_!6473)))
    (let (($x2863 (= ?x3570 ?x2628)))
    (let (($x3181 (or $x407 $x2863)))
    (let (($x3346 (= ?x4195 ?x3011)))
    (let (($x3507 (or $x405 $x3346)))
    (let (($x2679 (= ?x2481 ?x4224)))
    (let (($x2956 (or $x403 $x2679)))
    (let (($x3176 (= ?x3057 ?x3297)))
    (let (($x2715 (or $x401 $x3176)))
    (let (($x3156 (= ?x3590 ?x3364)))
    (let (($x2458 (or $x398 $x3156)))
    (let (($x2889 (and $x2458 $x2715 $x2956 $x3507 $x3181)))
    (let (($x2769 (not $x2889)))
    (let (($x2721 (or $x2769 $x2603)))
    (let (($x2879 (= S2_V4_!6483 S2_V4_!6457)))
    (let (($x3742 (or $x2990 $x2879)))
    (let (($x3363 (= S2_V4_!6473 S2_V4_!6457)))
    (let (($x3598 (or $x2497 $x3363)))
    (let (($x3162 (= S2_V4_!6462 S2_V4_!6483)))
    (let (($x2515 (or $x2506 $x3162)))
    (let (($x3253 (= S2_V4_!6462 S2_V4_!6473)))
    (let (($x2541 (or $x2604 $x3253)))
    (let (($x2743 (= S2_V4_!6462 S2_V4_!6457)))
    (let (($x2510 (or $x3068 $x2743)))
    (let (($x2891 (= E1_!6452 E1_!6463)))
    (let (($x3720 (= ?x2725 V4_0)))
    (let (($x161 (not R_E1_V4)))
    (let (($x3088 (or $x161 $x3720)))
    (let (($x3034 (= ?x2773 V5_0)))
    (let (($x159 (not R_E1_V5)))
    (let (($x3440 (or $x159 $x3034)))
    (let (($x2692 (= ?x3208 V2_0)))
    (let (($x157 (not R_E1_V2)))
    (let (($x2776 (or $x157 $x2692)))
    (let (($x3299 (and $x2776 $x3440 $x3088)))
    (let (($x2554 (not $x3299)))
    (let (($x2954 (or $x2554 $x2891)))
    (let (($x3713 (= E1_!6441 E1_!6463)))
    (let (($x4052 (= E1_!6441 E1_!6452)))
    (let (($x3260 (= V4_0 ?x2725)))
    (let (($x2566 (or $x161 $x3260)))
    (let (($x3436 (= V5_0 ?x2773)))
    (let (($x2656 (or $x159 $x3436)))
    (let (($x4179 (= V2_0 ?x3208)))
    (let (($x3506 (or $x157 $x4179)))
    (let (($x3139 (and $x3506 $x2656 $x2566)))
    (let (($x3186 (not $x3139)))
    (let (($x3770 (or $x3186 $x4052)))
    (let (($x2971 (= S1_V2_!6476 S1_V2_!6466)))
    (let (($x2829 (or $x2691 $x2971)))
    (let (($x2873 (= S1_V2_!6476 S1_V2_!6444)))
    (let (($x2974 (or $x3147 $x2873)))
    (let (($x2539 (= S1_V2_!6449 S1_V2_!6476)))
    (let (($x3798 (= ?x2838 ?x2734)))
    (let (($x3303 (or $x206 $x3798)))
    (let (($x4101 (= ?x2792 ?x3212)))
    (let (($x3283 (or $x204 $x4101)))
    (let (($x2936 (= ?x2952 ?x3664)))
    (let (($x3434 (or $x202 $x2936)))
    (let (($x2904 (= ?x3193 ?x4222)))
    (let (($x3478 (or $x200 $x2904)))
    (let (($x3078 (= ?x4025 ?x3808)))
    (let (($x2931 (or $x198 $x3078)))
    (let (($x2787 (and $x2931 $x3478 $x3434 $x3283 $x3303)))
    (let (($x3781 (not $x2787)))
    (let (($x2798 (or $x3781 $x2539)))
    (let (($x2775 (= S1_V2_!6449 S1_V2_!6466)))
    (let (($x2456 (= ?x2838 V4_0)))
    (let (($x2815 (or $x206 $x2456)))
    (let (($x3420 (= ?x2792 V5_0)))
    (let (($x2673 (or $x204 $x3420)))
    (let (($x3445 (= ?x2952 V2_0)))
    (let (($x2922 (or $x202 $x3445)))
    (let (($x2895 (= ?x3193 V3_0)))
    (let (($x2957 (or $x200 $x2895)))
    (let (($x2299 (= ?x4025 ?x2468)))
    (let (($x2802 (or $x198 $x2299)))
    (let (($x3315 (and $x2802 $x2957 $x2922 $x2673 $x2815)))
    (let (($x2821 (not $x3315)))
    (let (($x2447 (or $x2821 $x2775)))
    (let (($x3285 (= S1_V2_!6449 S1_V2_!6444)))
    (let (($x3085 (= ?x4025 ?x2768)))
    (let (($x2612 (or $x198 $x3085)))
    (let (($x2925 (and $x2612 $x2957 $x2922 $x2673 $x2815)))
    (let (($x3327 (not $x2925)))
    (let (($x2516 (or $x3327 $x3285)))
    (let (($x3050 (= S1_V2_!6444 S1_V2_!6466)))
    (let (($x3244 (or $x198 $x3713)))
    (let (($x3018 (not $x3244)))
    (let (($x2991 (or $x3018 $x3050)))
    (let (($x2801 (= S1_V3_!6465 S1_V3_!6475)))
    (let (($x3334 (or $x2800 $x2801)))
    (let (($x3399 (= S1_V3_!6448 S1_V3_!6475)))
    (let (($x2924 (or $x3781 $x3399)))
    (let (($x2482 (= S1_V3_!6448 S1_V3_!6465)))
    (let (($x2461 (or $x2821 $x2482)))
    (let (($x3505 (= S1_V3_!6448 S1_V3_!6443)))
    (let (($x2638 (or $x3327 $x3505)))
    (let (($x2553 (= S1_V3_!6443 S1_V3_!6475)))
    (let (($x2759 (or $x3705 $x2553)))
    (let (($x2684 (= S1_V3_!6443 S1_V3_!6465)))
    (let (($x2475 (or $x3018 $x2684)))
    (let (($x3164 (= S2_V5_!6472 S2_V5_!6482)))
    (let (($x2964 (or $x3998 $x3164)))
    (let (($x3428 (= S2_V5_!6461 S2_V5_!6482)))
    (let (($x4076 (or $x2506 $x3428)))
    (let (($x2704 (= S2_V5_!6461 S2_V5_!6472)))
    (let (($x3771 (or $x2604 $x2704)))
    (let (($x2998 (= S2_V5_!6461 S2_V5_!6456)))
    (let (($x3025 (or $x3068 $x2998)))
    (let (($x2830 (= S2_V5_!6456 S2_V5_!6482)))
    (let (($x2693 (or $x3245 $x2830)))
    (let (($x2900 (= S2_V5_!6456 S2_V5_!6472)))
    (let (($x3101 (= ?x2725 ?x2628)))
    (let (($x2453 (or $x407 $x3101)))
    (let (($x3366 (= ?x2773 ?x3011)))
    (let (($x3924 (or $x405 $x3366)))
    (let (($x2543 (= ?x3208 ?x4224)))
    (let (($x2886 (or $x403 $x2543)))
    (let (($x3203 (= ?x4155 ?x3297)))
    (let (($x3099 (or $x401 $x3203)))
    (let (($x3002 (= E1_!6452 ?x3364)))
    (let (($x3038 (or $x398 $x3002)))
    (let (($x3653 (and $x3038 $x3099 $x2886 $x3924 $x2453)))
    (let (($x4058 (not $x3653)))
    (let (($x2484 (or $x4058 $x2900)))
    (let (($x3466 (= S1_V1_!6474 S1_V1_!6464)))
    (let (($x4077 (or $x2691 $x3466)))
    (let (($x3594 (= S1_V1_!6474 S1_V1_!6447)))
    (let (($x2822 (or $x3252 $x3594)))
    (let (($x3704 (= S1_V1_!6474 S1_V1_!6442)))
    (let (($x3793 (or $x3147 $x3704)))
    (let (($x3077 (= S1_V1_!6447 S1_V1_!6464)))
    (let (($x2655 (or $x2821 $x3077)))
    (let (($x2530 (= S1_V1_!6447 S1_V1_!6442)))
    (let (($x2866 (or $x3327 $x2530)))
    (let (($x2633 (= S1_V1_!6442 S1_V1_!6464)))
    (let (($x2933 (or $x3018 $x2633)))
    (let
    (($x3828
      (and $x2933 $x2866 $x2655 $x3793 $x2822 $x4077 $x2484 $x2693 $x3025
      $x3771 $x4076 $x2964 $x2475 $x2759 $x2638 $x2461 $x2924 $x3334 $x2991
      $x2516 $x2447 $x2798 $x2974 $x2829 $x3770 $x3713 $x2954 $x2510 $x2541
      $x2515 $x3598 $x3742 $x2721 $x3895 $x3454 $x3645 $x3090 $x2445 $x2483
      $x2858 $x3472 $x2440 $x2642 $x3639 $x2761 $x2499 $x2729 $x3455 $x3243
      $x3094 $x2464 $x3610 $x2644 $x2946 $x2909 $x3774 $x2473 $x2861 $x3716
      $x3365 $x3237 $x3537 $x2921 $x2529 $x2948 $x3174 $x2511 $x2820 $x3261
      $x3809 $x3236)))
    (let (($x6054 (not $x3828))) (or $x6054 $x2446 $x2652)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let (($x90 (and W_S2_V5 R_E1_V5)))
 (let (($x89 (and W_S2_V2 R_E1_V2)))
 (let (($x2674 (or $x89 $x90 R_E1_V4)))
 (let (($x3325 (not $x2674)))
 (let (($x3197 (= DISJ_W_S2_R_E1 $x3325)))
 (let (($x81 (and W_S2_V5 R_S2_V5)))
 (let (($x80 (and W_S2_V2 R_S2_V2)))
 (let (($x79 (and W_S2_V3 R_S2_V3)))
 (let (($x78 (and W_S2_V1 R_S2_V1)))
 (let (($x113 (or $x78 $x79 $x80 $x81 R_S2_V4)))
 (let (($x114 (not $x113)))
 (let (($x115 (= DISJ_W_S2_R_S2 $x114)))
 (let (($x72 (and W_S2_V5 R_S1_V5)))
 (let (($x71 (and W_S2_V2 R_S1_V2)))
 (let (($x70 (and W_S2_V3 R_S1_V3)))
 (let (($x69 (and W_S2_V1 R_S1_V1)))
 (let (($x110 (or $x69 $x70 $x71 $x72 R_S1_V4)))
 (let (($x111 (not $x110)))
 (let (($x112 (= DISJ_W_S2_R_S1 $x111)))
 (let (($x63 (and W_S1_V5 W_S2_V5)))
 (let (($x3421 (or W_S2_V3 $x63 W_S1_V4)))
 (let (($x2469 (not $x3421)))
 (let (($x3897 (= DISJ_W_S1_W_S2 $x2469)))
 (let (($x155 (not R_E1_V3)))
 (let (($x37 (and W_S1_V4 R_S2_V4)))
 (let (($x35 (and W_S1_V5 R_S2_V5)))
 (let (($x3183 (or R_S2_V3 $x35 $x37)))
 (let (($x3855 (not $x3183)))
 (let (($x3462 (= DISJ_W_S1_R_S2 $x3855)))
 (let (($x23 (and W_S1_V4 R_S1_V4)))
 (let (($x20 (and W_S1_V5 R_S1_V5)))
 (let (($x3262 (or R_S1_V3 $x20 $x23)))
 (let (($x2785 (not $x3262)))
 (let (($x3412 (= DISJ_W_S1_R_S1 $x2785)))
 (let (($x2398 (not W_S2_V3)))
 (let (($x2387 (not W_S2_V2)))
 (let (($x407 (not R_S2_V4)))
 (let (($x398 (not R_S2_V1)))
 (let (($x6618 (and $x398 $x407 $x2387 $x2398 DISJ_W_S2_R_S1)))
 (let (($x405 (not R_S2_V5)))
 (let (($x4585 (and $x405 $x407 $x2398 DISJ_W_S2_R_S1)))
 (let (($x2353 (not W_S1_V5)))
 (let (($x6013 (and $x407 $x2353 $x2398 DISJ_W_S2_R_S1)))
 (let (($x5751 (and $x398 $x405 $x2387 $x2398 DISJ_W_S2_R_S1)))
 (let (($x2356 (not W_S1_V4)))
 (let (($x6084 (and $x405 $x2356 $x2398 DISJ_W_S2_R_S1)))
 (let (($x2390 (not W_S2_V5)))
 (let (($x6110 (and $x398 $x2387 $x2390 $x2398 DISJ_W_S2_R_S1)))
 (let (($x5527 (and DISJ_W_S1_W_S2 DISJ_W_S2_R_S1)))
 (let (($x401 (not R_S2_V3)))
 (let (($x6668 (and $x398 $x401 $x405 $x2387 DISJ_W_S2_R_S1)))
 (let (($x6901 (and $x398 $x401 $x407 $x2387 DISJ_W_S2_R_S1)))
 (let (($x4540 (and $x398 $x407 $x2387 $x2390 DISJ_W_S2_R_S1)))
 (let (($x6613 (and $x398 $x405 $x407 $x2387 DISJ_W_S2_R_S1)))
 (let (($x4273 (and $x398 $x401 $x2387 $x2390 DISJ_W_S2_R_S1)))
 (let (($x2384 (not W_S2_V1)))
 (let (($x3644 (and $x2384 $x2387)))
 (let (($x4922 (and $x401 $x407 $x2390 DISJ_W_S2_R_S1)))
 (let (($x3801 (and $x407 $x2390 $x2398 DISJ_W_S2_R_S1)))
 (let (($x4554 (and $x401 $x2356 $x2390 DISJ_W_S2_R_S1)))
 (let (($x2942 (and DISJ_W_S1_R_S2 DISJ_W_S2_R_S1)))
 (let (($x4368 (and $x2387 DISJ_W_S2_R_S2)))
 (let (($x3927 (and DISJ_W_S2_R_S1 DISJ_W_S2_R_S2)))
 (let
 (($x6996
   (or $x3927 $x4368 $x2942 $x4554 $x3801 $x4922 $x3644 $x4273 $x6613 $x4540
   $x6901 $x6668 $x5527 $x6110 $x6084 $x5751 $x6013 $x4585 $x6618)))
 (let (($x198 (not R_S1_V1)))
 (let (($x3875 (and $x198 DISJ_W_S1_R_S1)))
 (let (($x3184 (and $x2387 DISJ_W_S2_R_S1 DISJ_W_S1_R_S1)))
 (let (($x3290 (or $x3184 $x3644 $x3875)))
 (let (($x2350 (not W_S1_V2)))
 (let (($x2301 (not W_S1_V1)))
 (let (($x153 (not R_E1_V1)))
 (and DISJ_W_S1_R_E1 $x153 $x2301 $x2350 $x3290 $x6996 W_S1_V3 W_S2_V4 $x3412
 $x3462 $x155 $x3897 $x112 $x115 $x3197 $x5110 $x2486 $x3205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert (let (($x3927 (and DISJ_W_S2_R_S1 DISJ_W_S2_R_S2))) (not $x3927)))
(check-sat)
(exit)

