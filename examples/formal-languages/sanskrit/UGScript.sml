(*---------------------------------------------------------------------------*
 *       A Universal Grammar Machine (No Language-Specific Knowledge)        *
 *                                                                           *
 *                  Chun Tian, School of Computing,                          *
 *                Australian National University (2024)                      *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open stringTheory;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val theory_name = "UG";
val _ = new_theory theory_name;

(*---------------------------------------------------------------------------*
 *  Alphabet (for Indic scripts)                                             *
 *---------------------------------------------------------------------------*)

(* ISO 15919 (former: ITRANS) [1]

"Transliteration of Devanagari and related Indic scripts into Latin characters"

   NOTE: Only letters used (normally) by Sanskrit are defined so far. --binghe

       Vowels:  a, aa, i, ii, u, uu, vr, rr, vl; ee, ai, oo, au
  Semi-vowels:  y  r   l  v
   Consonants:  k  kh  g  gh  gn         [h]   (guttural)
                c  ch  j  jh  pn   [y]  [ps]   (palatal)
               rt rth rd rdh  rn   [r]  [rs]   (retroflex)
                t  th  d  dh   n   [l]   [s]   (dental)
                p  ph  b  bh   m   [v]         (labial)
    Sibilants:  ps rs  s   h
     Specials:  anu (anusvAra), vis (visarga), ava (avagraha)

 *)
Definition iso_a_def :
    iso_a = "a"
End

Definition iso_aa_def :
    iso_aa = "aa"
End

Definition iso_i_def :
    iso_i = "i"
End

Definition iso_ii_def :
    iso_ii = "ii"
End

Definition iso_u_def :
    iso_u = "u"
End

Definition iso_uu_def :
    iso_uu = "uu"
End

(* NOTE: "vr" stands for "vowel r" (dot under "r") *)
Definition iso_vr_def :
    iso_vr = ",r"
End

(* NOTE: "rr" is long vowel "r" (dot under "r"; minus above "r") *)
Definition iso_rr_def :
    iso_rr = ",rr"
End

Definition iso_vl_def :
    iso_vl = ",l"
End

(* NOTE: This is "e" in Sanskrit; The "e" is reserved for other Indic scripts *)
Definition iso_ee_def :
    iso_ee = "ee"
End

Definition iso_ai_def :
    iso_ai = "ai"
End

(* NOTE: This is "o" in Sanskrit; The "o" is reserved for other Indic scripts *)
Definition iso_oo_def :
    iso_oo = "oo"
End

Definition iso_au_def :
    iso_au = "au"
End

(* NOTE: This is called "anusvaara" (dot under "m") *)
Definition iso_anu_def :
    iso_anu = ";m"
End

(* NOTE: This is called "visarga" (dot under "h") *)
Definition iso_vis_def :
    iso_vis = ".h"
End

Definition iso_k_def :
    iso_k = "k"
End

Definition iso_kh_def :
    iso_kh = "kh"
End

Definition iso_g_def :
    iso_g = "g"
End

Definition iso_gh_def :
    iso_gh = "gh"
End

(* NOTE: "gn" standas for "guttural n" (dot above "n") *)
Definition iso_gn_def :
    iso_gn = ";n"
End

Definition iso_c_def :
    iso_c = "c"
End

Definition iso_ch_def :
    iso_ch = "ch"
End

Definition iso_j_def :
    iso_j = "j"
End

Definition iso_jh_def :
    iso_jh = "jh"
End

(* NOTE: "pn" stands for "palatal n" (tilde above "n") *)
Definition iso_pn_def :
    iso_pn = "~n"
End

(* NOTE: "rt" stands for "retroflex t" (dot under "t"), etc. *)
Definition iso_rt_def :
    iso_rt = ".t"
End

Definition iso_rth_def :
    iso_rth = ".th"
End

Definition iso_rd_def :
    iso_rd = ".d"
End

Definition iso_rdh_def :
    iso_rdh = ".dh"
End

Definition iso_rn_def :
    iso_rn = ".n"
End

Definition iso_t_def :
    iso_t = "t"
End

Definition iso_th_def :
    iso_th = "th"
End

Definition iso_d_def :
    iso_d = "d"
End

Definition iso_dh_def :
    iso_dh = "dh"
End

Definition iso_n_def :
    iso_n = "n"
End

Definition iso_p_def :
    iso_p = "p"
End

Definition iso_ph_def :
    iso_ph = "ph"
End

Definition iso_b_def :
    iso_b = "b"
End

Definition iso_bh_def :
    iso_bh = "bh"
End

Definition iso_m_def :
    iso_m = "m"
End

Definition iso_y_def :
    iso_y = "y"
End

Definition iso_r_def :
    iso_r = "r"
End

Definition iso_l_def :
    iso_l = "l"
End

Definition iso_v_def :
    iso_v = "v"
End

(* NOTE: "ps" stands for "palatal s" (accented "s") *)
Definition iso_ps_def :
    iso_ps = ";s"
End

(* NOTE: "rs" stands for "retroflex s" (dot under "s") *)
Definition iso_rs_def :
    iso_r = ".s"
End

Definition iso_s_def :
    iso_s = "s"
End

Definition iso_h_def :
    iso_h = "h"
End

(* NOTE: This is called "avagraha" or separation *)
Definition iso_ava_def :
    iso_ava = "'"
End

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
val _ = html_theory theory_name;

(* References:

   [1] https://en.wikipedia.org/wiki/ISO_15919
 *)
