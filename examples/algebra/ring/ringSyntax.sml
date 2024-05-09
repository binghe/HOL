structure ringSyntax :> ringSyntax =
struct

open HolKernel boolLib bossLib Parse;

fun is_ring_0 tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_const op' andalso let
        val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'
      in
        Thy = "ringLib" andalso Name = "ring_0"
      end
    end;

fun is_ring_1 tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_const op' andalso let
        val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'
      in
        Thy = "ringLib" andalso Name = "ring_1"
      end
    end;

fun is_ring_of_num tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_const op'' andalso let
          val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op''
        in
          Thy = "ringLib" andalso Name = "ring_of_num"
        end
      end
    end;

fun dest_ring_of_num tm = snd (dest_comb tm);

fun is_ring_of_int tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_const op'' andalso let
          val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op''
        in
          Thy = "ringLib" andalso Name = "ring_of_int"
        end
      end
    end;

fun dest_ring_of_int tm = snd (dest_comb tm);

fun is_ring_neg tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_const op'' andalso let
          val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op''
        in
          Thy = "ringLib" andalso Name = "ring_neg"
        end
      end
    end;

fun dest_ring_neg tm = snd (dest_comb tm);

fun is_ring_pow tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_pow"
          end
        end
      end
    end;

fun dest_ring_pow tm = let
    val (op',n) = dest_comb tm;
    val (_,x) = dest_comb op'
in
    (x,n)
end;

fun is_ring_add tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_add"
          end
        end
      end
    end;

fun dest_ring_add tm = let
    val (op',r) = dest_comb tm;
    val (_,l) = dest_comb op'
in
    (l,r)
end;

fun is_ring_sub tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_sub"
          end
        end
      end
    end;

fun dest_ring_sub tm = let
    val (op',r) = dest_comb tm;
    val (_,l) = dest_comb op'
in
    (l,r)
end;

fun is_ring_mul tm =
    is_comb tm andalso let
      val (op',_) = dest_comb tm
    in
      is_comb op' andalso let
        val (op'',_) = dest_comb op'
      in
        is_comb op'' andalso let
          val (op''',_) = dest_comb op''
        in
          is_const op''' andalso let
            val {Name: string, Thy: string, Ty: hol_type} = dest_thy_const op'''
          in
            Thy = "ringLib" andalso Name = "ring_mul"
          end
        end
      end
    end;

fun dest_ring_mul tm = let
    val (op',r) = dest_comb tm;
    val (_,l) = dest_comb op'
in
    (l,r)
end;

end (* struct *)
