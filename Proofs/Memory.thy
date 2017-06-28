theory Memory
imports
  "../AutoCorres/Impl"
  "../lib/ExtraLemmas"
begin

context sable_isa
begin

abbreviation "ALIGN_BITS \<equiv> 3"

definition
  mem_node_C_guard :: "mem_node_C ptr \<Rightarrow> bool"
where
  "mem_node_C_guard n \<equiv> c_null_guard n \<and> is_aligned (ptr_val n) ALIGN_BITS"

lemma[dest, intro]: "mem_node_C_guard p \<Longrightarrow> c_guard p"
unfolding mem_node_C_guard_def c_guard_def ptr_aligned_def is_aligned_def
by (auto simp add: align_of_def, unat_arith)

lemma contrapos: "(P \<longrightarrow> Q) = (\<not>Q \<longrightarrow> \<not>P)"
by blast

(*lemma heap_guard_set_array_addrs:
  "\<forall>p \<in> set (array_addrs heap_ptr HEAP_SIZE). mem_node_C_guard p"
apply (simp add: set_array_addrs mem_node_C_guard_def)
proof clarify
  fix k :: nat
  assume "k < HEAP_SIZE"
  show "c_null_guard (heap_ptr +\<^sub>p int k) \<and> is_aligned (ptr_val (heap_ptr +\<^sub>p int k)) ALIGN_BITS"
  proof
    have "{ptr_val (heap_ptr +\<^sub>p int k)..+size_of TYPE(mem_node_C)}
          \<subseteq> {ptr_val heap_ptr..+HEAP_SIZE * size_of TYPE(mem_node_C)}" (is "?P \<subseteq> ?H")
      using `k < HEAP_SIZE` apply (auto simp add: ptr_add_def intvl_def)
      apply (rule_tac x="k * 8 + ka" in exI, auto)
      done
    with heap_non_null show "c_null_guard (heap_ptr +\<^sub>p int k)"
      unfolding c_null_guard_def by blast
  next
    from heap_aligned have "is_aligned (symbol_table ''heap'' + of_nat k * (2 ^ ALIGN_BITS)) ALIGN_BITS"
      by (fastforce intro: Aligned.is_aligned_add_multI)
    thus "is_aligned (ptr_val (heap_ptr +\<^sub>p int k)) ALIGN_BITS"
      by (simp add: ptr_add_def)
  qed
qed*)
(*
abbreviation "HEAP_SIZE \<equiv> 1024" (* in mem_nodes *)
abbreviation "ALIGN_BITS \<equiv> 3"
abbreviation "heap_ptr \<equiv> Ptr (symbol_table ''heap'') :: mem_node_C ptr" *)
definition
  liftC :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
where
  "liftC st P \<equiv> \<lambda>s. \<forall>g. s = st g \<longrightarrow> P g"

lemma hoare_liftC_wp[wp]:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r s. \<forall>t. st s = t \<longrightarrow> Q r t\<rbrace> \<Longrightarrow> \<lbrace>liftC st P\<rbrace> exec_concrete st m \<lbrace>Q\<rbrace>"
unfolding liftC_def
apply wp
unfolding valid_def
apply auto
done

lemma hoare_liftC[intro]:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r s. \<forall>t. st s = t \<longrightarrow> liftC st (Q r) t\<rbrace> \<Longrightarrow>
   \<lbrace>liftC st P\<rbrace> exec_concrete st m \<lbrace>\<lambda>r s. liftC st (Q r) s\<rbrace>"
by wp

lemma fail'_wp: "\<lbrace>\<lambda>x. True\<rbrace> fail' \<lbrace>Q\<rbrace>"
unfolding fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def by wp

(* definition
  heap_invs_old :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> word32 \<Rightarrow> bool"
where
  "heap_invs s heap_ptr HEAP_SIZE \<equiv>
    (let node_size = mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) in
    node_size < HEAP_SIZE \<and> node_' s +\<^sub>p uint (node_size) = heap_ptr +\<^sub>p (HEAP_SIZE - 1) \<and>
    (\<forall>p \<in> {ptr_val (node_' s +\<^sub>p 1)..+unat node_size * size_of TYPE(mem_node_C)}.
      snd (hrs_htd (t_hrs_' s) p) = Map.empty)) \<and> is_aligned (ptr_val (node_' s)) ALIGN_BITS"
 *)
 
(*lemma heap_invs_node:
fixes s :: globals and i :: int
assumes invs: "heap_invs s" and lbound: "0 \<le> i"
    and bound: "i \<le> uint (size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) :: 32 word)"
shows "node_' s +\<^sub>p i \<in> set (array_addrs heap_ptr HEAP_SIZE)"
proof -
  let ?size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) :: 32 word"
  from invs have node_size: "node_' s +\<^sub>p uint ?size = heap_ptr +\<^sub>p (HEAP_SIZE - 1)"
                  and size: "?size < HEAP_SIZE"
    unfolding heap_invs_def Let_def by auto
  hence "ptr_val (node_' s) = ptr_val heap_ptr + (HEAP_SIZE - 1) * of_nat (size_of TYPE(mem_node_C))
                              - ?size * of_nat (size_of TYPE(mem_node_C))"
    unfolding ptr_add_def apply simp by uint_arith
  thus "node_' s +\<^sub>p i \<in> set (array_addrs heap_ptr HEAP_SIZE)"
    apply (simp add: set_array_addrs)
    apply (rule_tac x="(HEAP_SIZE - 1) + nat i - unat ?size" in exI)
    apply auto
    unfolding ptr_add_def
    apply simp
    apply (subst of_nat_diff)
    apply auto
    using size apply unat_arith
    using lbound apply simp
    apply (subgoal_tac "nat i \<le> nat (uint ?size)")
    apply (subst(asm) unat_def[symmetric], auto)
    using size and bound and lbound apply uint_arith
    done
qed

definition
  init_heap_P :: "unit ptr \<Rightarrow> 32 word \<Rightarrow> globals \<Rightarrow> bool"
where
  "init_heap_P p n s \<equiv> 0 \<notin> {ptr_val p..+unat n} \<and> is_aligned (ptr_val p) ALIGN_BITS \<and>
    (\<forall>node \<in> {ptr_val p..+unat n}. snd (hrs_htd (t_hrs_' s) node) = Map.empty)"

lemma init_heap'_invs:
  "\<lbrace>\<lambda>s. (init_heap_P s)\<rbrace> init_heap' \<lbrace>\<lambda>_ s. (heap_invs s)\<rbrace>!"
unfolding init_heap'_def heap_invs_def fail'_def
  FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def init_heap_P_def
apply wp
apply (auto simp add: ptr_add_def ptr_sub_def h_val_id intvl_self)
defer
using heap_ptr_guard apply (simp add: mem_node_C_guard_def)
using heap_ptr_guard apply blast
using heap_non_null and heap_aligned unfolding c_guard_def ptr_aligned_def c_null_guard_def
  is_aligned_def apply (simp add: align_of_array)
  using align_size_of[where 'a=mem_node_C] apply simp
  using dvd.dual_order.trans apply blast
proof -
  fix s :: globals and q :: "32 word"
  assume empty: "\<forall>p \<in> {symbol_table ''heap''..+8192}. snd (hrs_htd (t_hrs_' s) p) = Map.empty"
     and q: "q \<in> {symbol_table ''heap'' + 8..+8184}"
  from q have "q \<in> {symbol_table ''heap''..+8192}"
    by (rule_tac y=8 in intvl_plus_sub_offset, auto)
  with empty show "snd (hrs_htd (t_hrs_' s) q) = Map.empty" by blast
qed


lemma alloc'_no_fail: "0 < n \<Longrightarrow> no_fail (\<lambda>s. heap_invs s) (alloc' n)"
apply (rule validNF_no_fail [where Q="\<top>\<top>"])
unfolding alloc'_def Let_def
apply (simp add: h_val_field_from_bytes)
apply (wp fail'_wp)
apply (simp add: not_le)
proof -
  fix s :: globals
  let ?size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) :: 32 word"
  let ?blocks = "(n >> ALIGN_BITS) + 1 :: 32 word"
  assume "0 < n" and invs: "heap_invs s"
  from invs have node: "\<And>i. 0 \<le> i \<Longrightarrow> i \<le> uint ?size
        \<Longrightarrow> node_' s +\<^sub>p i \<in> set (array_addrs heap_ptr HEAP_SIZE)"
    using heap_invs_node by auto
  show "(?size \<le> ?blocks \<longrightarrow> c_guard (node_' s)) \<and>
         (?blocks < ?size \<longrightarrow> c_guard (node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS))) \<and> c_guard (node_' s))"
  proof safe
    show "c_guard (node_' s)" using node[of 0] and heap_guard_set_array_addrs
      unfolding ptr_add_def by auto
  next
    assume "?blocks < ?size"
    hence "uint (?blocks + 1) \<le> uint ?size" by uint_arith
    with node[of "uint (?blocks + 1)"] and heap_guard_set_array_addrs
      show "c_guard (node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)))" 
        unfolding ptr_add_def by auto
  next
    show "c_guard (node_' s)" using node[of 0] and heap_guard_set_array_addrs
      unfolding ptr_add_def by auto
  qed
qed

lemma alloc'_invs: "0 < n \<Longrightarrow> \<lbrace>\<lambda>s. heap_invs s\<rbrace> alloc' n \<lbrace>\<lambda>r s. heap_invs s\<rbrace>"
unfolding alloc'_def heap_invs_def Let_def
apply (simp add: h_val_field_from_bytes)
apply wp
apply (simp add: h_val_id not_le word_gt_a_gt_0)
apply (clarsimp simp add: heap_guard_set_array_addrs)
proof -
  fix s :: globals
  let ?size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) :: 32 word"
  let ?blocks = "(n >> ALIGN_BITS) + 1 :: 32 word"
  assume node_size: "node_' s +\<^sub>p uint ?size = heap_ptr +\<^sub>p 1023"
     and size: "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) < HEAP_SIZE"
     and blocks_size: "(n >> ALIGN_BITS) + 1 < ?size"
     and n: "0 < n"
     and empty: "\<forall>p \<in> {ptr_val (node_' s +\<^sub>p 1)..+unat ?size * 8}. snd (hrs_htd (t_hrs_' s) p) = Map.empty"
     and aligned: "is_aligned (ptr_val (node_' s)) ALIGN_BITS"
  from blocks_size have blocksp1_size: "?blocks + 1 \<le> ?size" by unat_arith
  from blocks_size and size have n_bound: "n < HEAP_SIZE * 8"
    by (simp add: shiftr3_is_div_8, unat_arith)
  show "?size - (2 + (n >> ALIGN_BITS)) < HEAP_SIZE \<and>
        node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)) +\<^sub>p uint (?size - (2 + (n >> ALIGN_BITS))) = heap_ptr +\<^sub>p 1023 \<and>
        (\<forall>p \<in> {ptr_val (node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)) +\<^sub>p 1)..+unat (?size - (2 + (n >> ALIGN_BITS))) * 8}.
             snd (hrs_htd (t_hrs_' s) p) = Map.empty) \<and>
             is_aligned (ptr_val (node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)))) ALIGN_BITS"
  proof safe
    show "node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)) +\<^sub>p uint (?size - (2 + (n >> ALIGN_BITS))) = heap_ptr +\<^sub>p 1023"
      using node_size unfolding ptr_add_def by unat_arith
  next
    show "?size - (2 + (n >> ALIGN_BITS)) < 0x400" using blocksp1_size and size
      by (auto, unat_arith)
  next
    fix p :: "32 word"
    assume p: "p \<in> {ptr_val (node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)) +\<^sub>p 1)..+unat (?size - (2 + (n >> ALIGN_BITS))) * 8}"
    moreover
    { have "unat (?size - (2 + (n >> ALIGN_BITS))) = unat ?size - unat (2 + (n >> ALIGN_BITS))"
        using size and blocks_size by unat_arith
      hence "unat (?size - (2 + (n >> ALIGN_BITS))) * 8 = unat ?size * 8 - unat (2 + (n >> ALIGN_BITS)) * 8" by simp }
    moreover
    { have "unat (2 + (n >> ALIGN_BITS)) * unat (8 :: 32 word) < 2 ^ len_of TYPE(32)"
        using n_bound by (simp add: shiftr3_is_div_8, unat_arith)
      hence "unat ((2 + (n >> ALIGN_BITS)) * 8) = unat (2 + (n >> ALIGN_BITS)) * unat (8 :: 32 word)"
        by (subst(asm) unat_mult_lem)
      hence "unat (2 + (n >> ALIGN_BITS)) * 8 = unat ((2 + (n >> ALIGN_BITS)) * 8)" by auto }
    ultimately have "p \<in> {ptr_val (node_' s +\<^sub>p 1) + ((2 + (n >> ALIGN_BITS)) * 8)..+
                            unat ?size * 8 - unat ((2 + (n >> ALIGN_BITS)) * 8)}"
      unfolding ptr_add_def by simp
    hence "p \<in> {ptr_val (node_' s +\<^sub>p 1)..+unat ?size * 8}"
      by (drule_tac y="(2 + (n >> ALIGN_BITS)) * 8" in intvl_plus_sub_offset)
    with empty show "snd (hrs_htd (t_hrs_' s) p) = Map.empty" by blast
  next
    from aligned have "is_aligned (ptr_val (node_' s) + 2 * 2 ^ ALIGN_BITS) ALIGN_BITS"
      by (fastforce intro: Aligned.is_aligned_add_multI)
    hence "is_aligned ((ptr_val (node_' s) + 0x10) + (n >> 3) * 2 ^ ALIGN_BITS) ALIGN_BITS"
      by (fastforce intro: Aligned.is_aligned_add_multI)
    thus "is_aligned (ptr_val (node_' s +\<^sub>p uint (2 + (n >> ALIGN_BITS)))) ALIGN_BITS"
      by (simp add: ptr_add_def is_num_normalize(1))
  qed
qed*)
definition nodeFree :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "nodeFree s node \<equiv>
    (let size = (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) node)) && scast (~~ MEM_NODE_OCCUPIED_FLAG) in
    \<forall>p \<in> {ptr_val (node +\<^sub>p 1)..+unat size * size_of TYPE(mem_node_C)}.
      snd (hrs_htd (t_hrs_' s) p) = Map.empty)"
    
value "if ((1::nat) > 2) then a else b"
definition nodeValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "nodeValid s node = 
  (let occupied = (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) node)) && scast  MEM_NODE_OCCUPIED_FLAG in
   let next = (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) node)) in
   let size = (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) node)) && scast (~~ MEM_NODE_OCCUPIED_FLAG) in
   c_guard node \<and> unat (ptr_val (node +\<^sub>p 1)) + unat (size * 8) \<le> 
    ( if (next \<noteq> NULL) then unat (ptr_val next) else 2 ^ len_of (TYPE(32))) \<and>
   unat (size) * 8 < 2 ^ len_of (TYPE(32)) \<and>
   (occupied = 0 \<longrightarrow> nodeFree s node) \<and> (next \<noteq> NULL \<longrightarrow> next > node) )"

function nodesValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "nodesValid s heap =
  (let next = (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) heap)) in 
    nodeValid s heap \<and> (next \<noteq> NULL \<longrightarrow>  nodesValid s next))"
by pat_completeness auto


definition
  heap_invs :: "globals \<Rightarrow> unit ptr \<Rightarrow> bool"
where
  "heap_invs s heap \<equiv> nodesValid s (ptr_coerce heap)"

abbreviation node_size
where "node_size s n \<equiv> size_C (h_val (hrs_mem (t_hrs_' s)) n)"
abbreviation node_next
where "node_next s n \<equiv> next_C (h_val (hrs_mem (t_hrs_' s)) n)" 

abbreviation update_node :: " globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C \<Rightarrow> globals"
where "update_node s n node_val \<equiv>
  (t_hrs_'_update (hrs_mem_update (heap_update n  node_val)) s)"

lemma updated_node_val: 
"h_val (hrs_mem (t_hrs_' (update_node s n node_val))) n = node_val"
by (simp add: h_val_heap_update hrs_mem_update)

lemma updated_node_size:
  "node_size (update_node s n (mem_node_C nodeSize next)) n = nodeSize"
using sable_isa.updated_node_val by auto
lemma updated_node_next:
  "node_next (update_node s n (mem_node_C nodeSize next)) n = next"
using sable_isa.updated_node_val by auto


lemma heap_invs_not_null :"heap_invs s heap \<Longrightarrow> heap \<noteq> NULL" 
sorry
value "mem_node_C"
function test' :: "nat \<Rightarrow> nat"
where "test' 0 = 0"
     | "test' (Suc 0) = 1"
     | "test' (Suc (Suc n)) = test' (Suc n) + test' n"     
by pat_completeness auto
termination by lexicographic_order
value "test' 1"

function reachable' :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "reachable' s heap n =( let heap_next = (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) heap))
      in (heap = NULL \<longrightarrow> n = NULL) \<and>
      (heap \<noteq> NULL \<longrightarrow> heap = n \<or>
      (ptr_val heap_next > ptr_val heap \<and> reachable' s heap_next n)))"
by pat_completeness auto
termination apply (relation "measure (\<lambda> (s,heap,n). unat (ptr_val n) - unat (ptr_val heap))")
apply auto
sorry

function reachable :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "reachable s heap n = (heap \<noteq> NULL \<and>
      (heap = n \<or> 
       (\<exists> n'. n = (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) n')) \<and>
          ptr_val n > ptr_val n' \<and> reachable s heap n')))"
by pat_completeness auto
termination apply (relation "measure (\<lambda> (s,heap,n). unat (ptr_val n))")
apply auto
oops

abbreviation hrs_the_same_at
where "hrs_the_same_at s s' p \<equiv>
  fst (t_hrs_' s) p = fst (t_hrs_' s') p \<and> snd (t_hrs_' s) p = snd (t_hrs_' s') p"

lemma updated_node_hrs_the_same_elsewhere :
  " x \<ge> ptr_val (p +\<^sub>p 1) \<or> x < ptr_val p \<Longrightarrow> hrs_the_same_at s (update_node s p new_node) x" 
apply auto
sorry
lemma updated_node_blahblah:
  "x \<ge> ptr_val (p+\<^sub>p 1) \<and> x \<ge> ptr_val (q +\<^sub>p 1) \<Longrightarrow> 
    hrs_the_same_at s (update_node (update_node s p new_node_1) q new_node_2 ) x"
using updated_node_hrs_the_same_elsewhere
by presburger

lemma updated_node_blahblah_2:
  "x < ptr_val p \<and> x < ptr_val q \<Longrightarrow> 
    hrs_the_same_at s (update_node (update_node s p new_node_1) q new_node_2 ) x"
using updated_node_hrs_the_same_elsewhere
by presburger

lemma 
  "(update_node (update_node s p new_node_1) q new_node_2 )
  = t_hrs_'_update (hrs_mem_update  
          (heap_update q new_node_2) \<circ> hrs_mem_update (heap_update p new_node_1))
          s"
by simp
          
function path :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr list"
where "path s heap last_node = (if (heap = NULL) then [] 
       else if ptr_val (node_next s heap) > ptr_val heap then heap # (path s (node_next s heap) last_node)
          else [])"
by pat_completeness auto
termination apply (relation "measure (\<lambda> (s,heap,n).unat (ptr_val n) - unat (ptr_val heap))")
apply simp
sorry
(* where  "path s NULL _ = []"
      |"path s heap last_node = heap # (path s (node_next s heap) last_node)"
 *)

lemma "\<forall> p . p \<ge> ptr_val heap \<and> p < ptr_val (last_node +\<^sub>p 1) \<longrightarrow>  fst (t_hrs_' s) p = fst (t_hrs_' s') p
          \<and> snd (t_hrs_' s) p= snd (t_hrs_' s') p
       \<Longrightarrow>  path s heap last_node = path s' heap last_node"    
sorry


lemma "nodesValid s heap \<Longrightarrow>
       \<forall> p . p \<ge> ptr_val heap \<and> p < ptr_val (last_node +\<^sub>p 1) \<longrightarrow>  fst (t_hrs_' s) p = fst (t_hrs_' s') p
          \<and> snd (t_hrs_' s) p= snd (t_hrs_' s') p
       \<Longrightarrow> \<forall> n \<in> set (path s heap last_node). nodeValid s' n"
sorry
      
lemma self_reachable: "n \<noteq> NULL \<Longrightarrow> reachable s n n"
sorry

lemma reachable_trans :
  "reachable s heap n \<Longrightarrow> n \<noteq> NULL \<Longrightarrow> reachable s heap (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) n))" 
sorry
print_record globals
print_record lifted_globals
thm whileLoop_def
thm alloc'_def
thm heap_invs_def

lemma nodesValid_trans_back: "nodeValid s node \<Longrightarrow> nodesValid s next \<Longrightarrow> node_next s node = next \<Longrightarrow>
       nodesValid s node"
sorry

lemma invs_reachable_imp_nodes_valid: "heap_invs s heap \<Longrightarrow> reachable s (ptr_coerce heap) node
      \<Longrightarrow> node \<noteq> Null \<Longrightarrow> nodesValid s node"
unfolding heap_invs_def using "nodesValid.pinduct"
sorry

lemma invs_reachable_imp_valid: "heap_invs s heap \<Longrightarrow> reachable s (ptr_coerce heap) node
      \<Longrightarrow> node \<noteq> Null \<Longrightarrow> nodeValid s node"
unfolding heap_invs_def using "nodesValid.pinduct"
sorry

lemma next_reachable : "reachable s heap n \<Longrightarrow> c_guard n \<Longrightarrow>
  reachable s heap (next_C (h_val (hrs_mem (t_hrs_' s)) n))"
sorry

lemma w_mult_pres_le:"(a:: word32) \<le> (b :: word32) \<Longrightarrow> 
        x > 0 \<Longrightarrow> 
        unat b * unat (x:: word32) < 2 ^ 32 \<Longrightarrow>
        a * x \<le> b * x"
sorry

lemma l10: "unat x + unat y < 2 ^ 32 \<Longrightarrow>y \<noteq> 0 \<Longrightarrow> (x:: word32) div ( y :: word32) * y + y \<ge> x"
apply unat_arith
apply auto
sorry

lemma l11:"((x::word32) || (scast (y::  32 signed word))) && (scast (~~y)) = x && (scast (~~y))"
apply (subst word_ao_dist)
proof -
  have " ((scast y)::word32) && scast (~~ y) = 0" unfolding scast_def sorry
  hence " x && scast (~~ y) || scast y && scast (~~ y) = x && scast (~~ y) || 0"
    by (simp add: \<open>scast y && scast (~~ y) = 0\<close>)
  thus "x && scast (~~ y) || scast y && scast (~~ y) = x && scast (~~ y)"  by simp
qed

lemma mask_l11 : "(x::word32) &&  flag = 0
  \<Longrightarrow> x &&  (~~flag) = x"
by (simp add: mask_eq_0_eq_x)

lemma mask_sw32_eq_0_eq_x :
  assumes "(x::word32) && scast (flag:: 32 signed word) = 0"
  shows " x && scast (~~flag) = x"
proof -
  let ?flag_w32 = "(scast flag)::word32"
  let ?neg_flag_w32 =  "scast (~~flag) :: word32"
  have l1[simp]: "?neg_flag_w32 = ~~ ?flag_w32" sorry
  thus ?thesis using assms by (simp add: mask_eq_0_eq_x)
qed

lemma MEM_NODE_OCCUPIED_FLAG_not_zero:
  "MEM_NODE_OCCUPIED_FLAG \<noteq> (0:: 32 signed word)" unfolding MEM_NODE_OCCUPIED_FLAG_def by auto

declare [[show_types]] 
declare [[show_sorts]]
(* declare [[show_consts]] *)
thm alloc'_def
thm nodeValid_def
print_record globals

lemma nodesValid_not_null:
  "nodesValid s heap \<Longrightarrow> heap \<noteq> NULL"
sorry
lemma nodesValid_l1:
assumes "nodesValid s heap" 
    and "nodeValid s' heap"
    and "\<forall>x. x \<ge> ptr_val (heap +\<^sub>p 1) \<longrightarrow> fst (t_hrs_' s) x = fst (t_hrs_' s') x
            \<and> snd (t_hrs_' s) x= snd (t_hrs_' s') x"
shows "nodesValid s' heap"
sorry

lemma nodesValid_l2:
      "\<forall> p \<in> set (path s heap node). nodeValid s p \<Longrightarrow>
       reachable s heap node \<Longrightarrow>
       nodesValid s node \<Longrightarrow>
       nodesValid s heap"
sorry

lemma alloc'_invs:
fixes size_bytes:: "32 word" and heap:: "unit ptr"
shows "\<lbrace>\<lambda>s. heap_invs s heap \<rbrace> alloc' heap size_bytes \<lbrace> \<lambda>r s. heap_invs s heap \<rbrace>"
unfolding alloc'_def Let_def 
apply (simp add: h_val_field_from_bytes)
apply (subst whileLoop_add_inv 
       [where I="\<lambda> (n,r) s. heap_invs s heap \<and> reachable s (ptr_coerce heap) n
                  \<and> (r=0 \<longrightarrow> n = NULL \<or> ((size_bytes >> 3) + 1
                        \<le> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast (~~ MEM_NODE_OCCUPIED_FLAG)
                     \<and> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast MEM_NODE_OCCUPIED_FLAG = 0))" 
        and M="\<lambda> ((n,y),s). ptr_val n"])
apply (wp fail'_wp)
apply auto
apply (rule next_reachable, auto)
apply (drule next_reachable, auto)
apply (rule next_reachable, auto)
defer
apply (drule next_reachable, solves auto, solves auto)+
defer 
apply (drule next_reachable, auto) 
defer
proof -
  fix a::"mem_node_C ptr"
  fix s::globals
  assume invs: "heap_invs s heap"
    and node_free :"node_size s a && scast MEM_NODE_OCCUPIED_FLAG = 0"
    and reachable: "reachable s (ptr_coerce heap) a"
    and "a \<noteq> NULL"
  from invs and reachable and `a \<noteq> NULL` have "nodesValid s a"
    using invs_reachable_imp_nodes_valid by simp
  let ?new_size_simplified = "(node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG) ||  scast MEM_NODE_OCCUPIED_FLAG)"
  let ?new_s = "(update_node s a (mem_node_C
                (node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG) ||  scast MEM_NODE_OCCUPIED_FLAG)
                (node_next s a)))"
  let ?new_size = "(node_size ?new_s a) "
  have "node_next ?new_s a = node_next s a" using updated_node_next by auto
  have "?new_size = ?new_size_simplified" using updated_node_size by auto
  have "?new_size_simplified  && scast (~~MEM_NODE_OCCUPIED_FLAG) =
    node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG) && scast (~~MEM_NODE_OCCUPIED_FLAG)"
    using l11 by (simp add: word_bw_assocs(1))
  hence "node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG) =
        ?new_size  && scast (~~MEM_NODE_OCCUPIED_FLAG)"
    apply (subst `?new_size = ?new_size_simplified`) by simp
  moreover have new_node_occupied: "?new_size_simplified && scast MEM_NODE_OCCUPIED_FLAG = scast MEM_NODE_OCCUPIED_FLAG"
    unfolding MEM_NODE_OCCUPIED_FLAG_def using word_ao_absorbs(5) by blast
  moreover from invs and reachable and `a \<noteq> NULL` have "nodeValid s a" using invs_reachable_imp_valid by blast
  moreover have "(?new_size && scast MEM_NODE_OCCUPIED_FLAG = (0::32 word) \<longrightarrow> nodeFree ?new_s a)" 
    apply (simp add: `?new_size = ?new_size_simplified`)
    using MEM_NODE_OCCUPIED_FLAG_not_zero
    by (metis calculation(2) h_val_heap_update hrs_update(1) scast_0 scast_scast_id(2) size_C.size_C_def)
  moreover from `nodeValid s a` have "c_guard a \<and>
       unat (ptr_val (a +\<^sub>p (1::int))) + unat ((?new_size && scast (~~MEM_NODE_OCCUPIED_FLAG)) * (8::32 word)) 
        \<le> ( if ((node_next ?new_s a) \<noteq> NULL) then unat (ptr_val (node_next ?new_s a)) else 2 ^ len_of (TYPE(32))) 
        \<and> unat (?new_size && scast (~~MEM_NODE_OCCUPIED_FLAG)) * (8::nat) < (2::nat) ^ len_of TYPE(32)" 
       unfolding nodeValid_def
       apply (subst `node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG) =
        ?new_size  && scast (~~MEM_NODE_OCCUPIED_FLAG)`)
       apply (subst ` node_next ?new_s a = node_next s a`)
       using calculation(1)
       by (metis next_C.next_C_def sable_isa.updated_node_val)       
  moreover from `nodeValid s a` have "node_next ?new_s a \<noteq> NULL \<longrightarrow> a < node_next ?new_s a"
    apply (subst `node_next ?new_s a = node_next s a`)+ by (meson nodeValid_def)     
  ultimately have "nodeValid ?new_s a" unfolding nodeValid_def
    by presburger 
  moreover have "\<forall> x. x \<ge> ptr_val (a +\<^sub>p 1) \<longrightarrow>  hrs_the_same_at s ?new_s x"
    using updated_node_hrs_the_same_elsewhere by simp
  ultimately have "nodesValid ?new_s a" using  `nodesValid s a`  nodesValid_l1 by blast 
  moreover have "\<forall> p \<in> set (path ?new_s (ptr_coerce heap) a). nodeValid ?new_s p"
  sorry
  moreover have "reachable ?new_s (ptr_coerce heap) a"
  sorry
  ultimately have "nodesValid ?new_s (ptr_coerce heap)" using nodesValid_l2 by blast
  thus "heap_invs ?new_s heap" unfolding heap_invs_def by blast
next
defer defer defer defer
  fix a::"mem_node_C ptr"
  fix s::globals
  let ?new_size =  "((size_bytes >> (3::nat)) + (1::32 word) || scast MEM_NODE_OCCUPIED_FLAG)"
  let ?new_next = "(a +\<^sub>p uint ((2::32 word) + (size_bytes >> (3::nat))))"
  let ?new_next_size ="((size_C (h_val (hrs_mem (t_hrs_' s)) a) && scast (~~ MEM_NODE_OCCUPIED_FLAG)) -
                 ((2::32 word) + (size_bytes >> (3::nat))) &&
                 scast (~~ MEM_NODE_OCCUPIED_FLAG))"
  let ?next = "(next_C (h_val (hrs_mem (t_hrs_' s)) a))"
  let ?new_s = "(t_hrs_'_update
          (hrs_mem_update
            (heap_update a (mem_node_C ?new_size ?new_next)) \<circ>
           hrs_mem_update
            (heap_update ?new_next (mem_node_C ?new_next_size ?next)))
          s)"
  let ?new_s_simp = 
    "(update_node (update_node s ?new_next (mem_node_C ?new_next_size ?next)) a (mem_node_C ?new_size ?new_next))" 
  have new_s_simp[simp]: "?new_s_simp = ?new_s" by simp
  assume "heap_invs s heap"
       "reachable s (ptr_coerce heap) a"
       "(size_bytes >> 3) + 1  \<le> node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG)"
       "node_size s a && scast MEM_NODE_OCCUPIED_FLAG = 0"
       "(size_bytes >> 3) + 1  < node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG)"
       "c_guard a"
       "c_guard ?new_next"
  have "nodeValid s a" sorry 
  hence "
  have "nodeValid ?new_s ?new_next" unfolding nodeValid_def sorry
  
  hence "nodesValid ?new_s ?new_next" sorry
  
  moreover have "nodeValid ?new_s a" sorry
  
  moreover have "node_next ?new_s a = ?new_next" sorry
  
  ultimately have "nodesValid ?new_s a" using nodesValid_trans_back by blast
  from `nodeValid s a` and `c_guard ?next`
  have "unat (ptr_val (a +\<^sub>p 1)) + unat ((node_size s a) && scast (~~ MEM_NODE_OCCUPIED_FLAG) * 8) \<le> 
     unat (ptr_val ?next)"
  moreover 
  {have "\<forall> p. p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s_simp p"
     apply clarify
     apply (rule updated_node_blahblah_2)
     proof auto
     fix p:: word32
     show "p < ptr_val a \<Longrightarrow> p < ptr_val (a +\<^sub>p uint (2 + (size_bytes >> 3)))"
  
  hence "\<forall> p \<in> set (path ?new_s (ptr_coerce heap) a). nodeValid ?new_s p" sorry
  }
  
  moreover have "reachable ?new_s (ptr_coerce heap) a" sorry
  
  ultimately have "nodesValid ?new_s (ptr_coerce heap)" using nodesValid_l2 by blast
  thus "heap_invs ?new_s  heap" unfolding heap_invs_def by auto
next
 show "\<lbrace>\<lambda>s .heap_invs s heap\<rbrace>
    condition (\<lambda>s::globals. heap \<noteq> NULL)
      (do y::unit \<leftarrow> guard (\<lambda> s003::globals. c_guard (ptr_coerce heap));
          ret::bool \<leftarrow>
          gets (\<lambda>s::globals.
                   size_C (h_val (hrs_mem (t_hrs_' s)) (ptr_coerce heap))
                   < (size_bytes >> (3::nat)) + (1::32 word));
          condition (\<lambda>s::globals. ret)
            (return (1::int))
            (gets (\<lambda>s::globals.
                      if size_C (h_val (hrs_mem (t_hrs_' s)) (ptr_coerce heap)) &&
                         scast MEM_NODE_OCCUPIED_FLAG \<noteq>
                         (0::32 word)
                      then 1::int else (0::int)))
       od)
      (return (0::int)) 
    \<lbrace>\<lambda>(ret::int) a::globals.
        heap_invs a heap \<and>
        reachable a (ptr_coerce heap) (ptr_coerce heap) \<and>
        (ret = (0::int) \<longrightarrow>
         heap = NULL \<or>
         (size_bytes >> (3::nat)) + (1::32 word)
         \<le> size_C (h_val (hrs_mem (t_hrs_' a)) (ptr_coerce heap)) &&
            scast (~~ MEM_NODE_OCCUPIED_FLAG) \<and>
         size_C (h_val (hrs_mem (t_hrs_' a)) (ptr_coerce heap)) && scast MEM_NODE_OCCUPIED_FLAG =
         (0::32 word))\<rbrace>" 
  apply wp
  apply auto
  apply (rule self_reachable, simp)
  unfolding heap_invs_def
  apply (drule nodesValid_not_null, simp)
  apply (rule self_reachable, simp)
  apply (frule mask_sw32_eq_0_eq_x) 
  apply (solves unat_arith)
  by (drule nodesValid_not_null, simp)
next
  show "\<lbrace>\<lambda>s::globals. heap_invs s heap\<rbrace>
    when (\<not> (0::32 word) < size_bytes) (exec_abstract lift_global_heap fail') 
    \<lbrace>\<lambda>r s. heap_invs s heap\<rbrace>"
  apply (wp fail'_wp)
  by auto
next
  show "\<And>(a::mem_node_C ptr) (b::int) s::globals.
       heap_invs s heap \<Longrightarrow>
       reachable s (ptr_coerce heap) a \<Longrightarrow>
       b \<noteq> (0::int) \<Longrightarrow>
       \<not> size_C (h_val (hrs_mem (t_hrs_' s)) (next_C (h_val (hrs_mem (t_hrs_' s)) a)))
          < (size_bytes >> (3::nat)) + (1::32 word) \<Longrightarrow>
       next_C (h_val (hrs_mem (t_hrs_' s)) a) \<noteq> NULL \<Longrightarrow>
       c_guard a \<Longrightarrow>
       c_guard (next_C (h_val (hrs_mem (t_hrs_' s)) a)) \<Longrightarrow>
       size_C (h_val (hrs_mem (t_hrs_' s)) (next_C (h_val (hrs_mem (t_hrs_' s)) a))) &&
       scast MEM_NODE_OCCUPIED_FLAG =
       (0::32 word) \<Longrightarrow>
       (size_bytes >> (3::nat)) + (1::32 word)
       \<le> size_C (h_val (hrs_mem (t_hrs_' s)) (next_C (h_val (hrs_mem (t_hrs_' s)) a))) &&
          scast (~~ MEM_NODE_OCCUPIED_FLAG)"
  by (frule mask_sw32_eq_0_eq_x,simp)    
next
  show "\<And>(a::mem_node_C ptr) (b::int) s::globals.
       b \<noteq> (0::int) \<Longrightarrow>
       heap_invs s heap \<Longrightarrow>
       reachable s (ptr_coerce heap) a \<Longrightarrow>
       (size_bytes >> (3::nat)) + (1::32 word)
       \<le> size_C (h_val (hrs_mem (t_hrs_' s)) a) && scast (~~ MEM_NODE_OCCUPIED_FLAG) \<Longrightarrow>
       size_C (h_val (hrs_mem (t_hrs_' s)) a) && scast MEM_NODE_OCCUPIED_FLAG = (0::32 word) \<Longrightarrow>
       \<not> size_C (h_val (hrs_mem (t_hrs_' s)) (next_C (h_val (hrs_mem (t_hrs_' s)) a)))
          < (size_bytes >> (3::nat)) + (1::32 word) \<Longrightarrow>
       next_C (h_val (hrs_mem (t_hrs_' s)) a) \<noteq> NULL \<Longrightarrow>
       c_guard a \<Longrightarrow>
       c_guard (next_C (h_val (hrs_mem (t_hrs_' s)) a)) \<Longrightarrow>
       size_C (h_val (hrs_mem (t_hrs_' s)) (next_C (h_val (hrs_mem (t_hrs_' s)) a))) &&
       scast MEM_NODE_OCCUPIED_FLAG =
       (0::32 word) \<Longrightarrow>
       (size_bytes >> (3::nat)) + (1::32 word)
       \<le> size_C (h_val (hrs_mem (t_hrs_' s)) (next_C (h_val (hrs_mem (t_hrs_' s)) a))) &&
          scast (~~ MEM_NODE_OCCUPIED_FLAG)"
  apply (frule mask_sw32_eq_0_eq_x)
  apply (frule mask_sw32_eq_0_eq_x)
  using mask_sw32_eq_0_eq_x by auto
qed

lemma test123: "((x :: nat) > 10 \<longrightarrow> x ^ 2 > 89) \<and> (x > 10 \<longrightarrow> x^2 > 90)"

{ fix y
  assume "(y::nat) > 10"
 hence l:"y ^ 2 > 90" sorry}
note l = this
from l show "(10::nat) < x \<longrightarrow> (90::nat) < x\<^sup>2" by blast
next
from l show "(10::nat) < x \<longrightarrow> (90::nat) < x\<^sup>2" by blast
sorry

lemma alloc'_hoare_helper:
 fixes size_bytes heap
 assumes n:"size_of TYPE('a) \<le> unat size_bytes"
 and align: "align_of TYPE('a) dvd (2 ^ ALIGN_BITS)"
 shows "\<And>(node::mem_node_C ptr) s::globals.
       heap_invs s heap \<Longrightarrow>
       reachable s (ptr_coerce heap) node \<Longrightarrow>
       (size_bytes >> (3::nat)) + (1::32 word)
       \<le> size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast (~~ MEM_NODE_OCCUPIED_FLAG) \<Longrightarrow>
       size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast MEM_NODE_OCCUPIED_FLAG = (0::32 word) \<Longrightarrow>
       node \<noteq> NULL \<Longrightarrow>
       c_guard node \<Longrightarrow>
      
       ptr_val (node +\<^sub>p (1::int)) \<noteq> (0::32 word) \<Longrightarrow>
       heap_ptr_valid (ptr_retyp ((ptr_coerce (node +\<^sub>p (1)))::'a::mem_type ptr) (hrs_htd (t_hrs_' s)))
        ((ptr_coerce (node +\<^sub>p (1::int))):: 'a ptr)"
proof -
  fix s :: globals fix node ::"mem_node_C ptr"
  let ?ptrc = "ptr_coerce (node  +\<^sub>p 1) :: 'a ptr"
  let ?node_size = "size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast (~~ MEM_NODE_OCCUPIED_FLAG) :: 32 word"
  let ?blocks = "(size_bytes >> 3) + 1 :: 32 word"
  let ?heap_ptr = "ptr_coerce heap :: mem_node_C ptr"
  assume "ptr_val (node +\<^sub>p 1) \<noteq> 0" and invs: "heap_invs s heap"
     and blocks_size: "?blocks \<le> ?node_size"
     and "reachable s (ptr_coerce heap) node"
     and node_empty: "size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast MEM_NODE_OCCUPIED_FLAG = 0"
     and  "node \<noteq> NULL"
     and "c_guard node"
     and "ptr_val (node +\<^sub>p 1) \<noteq> 0"
  (* from invs have node: "node \<in> set (array_addrs heap_ptr HEAP_SIZE)"
    using heap_invs_node[where i=0] by auto *)
  have aligned: "is_aligned (ptr_val (node)) ALIGN_BITS" sorry 
  from`heap_invs s heap` and `reachable s (ptr_coerce heap) node`
   have "nodeValid s node" sorry
  hence nodeFree:"nodeFree s node" using node_empty unfolding nodeValid_def by meson 
  hence empty: "\<forall>p\<in>{ptr_val (node +\<^sub>p 1)..+unat ?node_size * 8}.
                            snd (hrs_htd (t_hrs_' s) p) = Map.empty"
   unfolding nodeFree_def by auto
  have node_size: "unat (ptr_val (node +\<^sub>p 1)) + unat (?node_size * 8) \<le> 2 ^ len_of (TYPE(32))"
    using `nodeValid s node` unfolding nodeValid_def  by meson  
  have "0 \<notin> {ptr_val (node +\<^sub>p 1)..+ unat (?node_size * 8)}"
  proof (rule ccontr)
    assume "\<not> 0 \<notin> {ptr_val (node +\<^sub>p 1)..+ unat (?node_size * 8)}"
    hence "0 \<in> {ptr_val (node +\<^sub>p 1)..+ unat (?node_size * 8)}" by simp
    then obtain k where 0:"0=ptr_val (node +\<^sub>p 1) + of_nat k \<and> k < unat (?node_size * 8)"
      using intvlD by blast
    hence "k \<le> unat (?node_size * 8) -1 " by (simp add: nat_le_Suc_less_imp)
    moreover from node_size have "unat (ptr_val (node +\<^sub>p 1)) + (unat (?node_size * 8) - 1) < 2 ^ len_of (TYPE(32))"
      by unat_arith
    ultimately have "unat (ptr_val (node +\<^sub>p 1)) +  k <  2 ^ len_of (TYPE(32))" by arith
    hence "ptr_val (node +\<^sub>p 1) + of_nat k \<ge> ptr_val (node +\<^sub>p 1)"
      by (metis add.commute add_lessD1 no_olen_add_nat unat_of_nat32 word_bits_def)
    hence "ptr_val (node +\<^sub>p 1) + of_nat k \<noteq> 0" using `ptr_val (node +\<^sub>p 1) \<noteq> 0` by auto
    thus False using 0 by force
  qed 
  hence zero_not_in_node_range: "0 \<notin> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat (?node_size * 8)}" by simp
  have "unat ?node_size * 8 < 2 ^ len_of (TYPE(32))"
    using `nodeValid s node` unfolding nodeValid_def by meson
  show "heap_ptr_valid (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) ?ptrc"
    unfolding heap_ptr_valid_def c_guard_def  
  proof safe
    show "valid_simple_footprint (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) (ptr_val ?ptrc)
          (typ_uinfo_t TYPE('a))"
    apply (rule TypHeapSimple.valid_simple_footprint_ptr_retyp) defer
    apply (simp, metis Suc_le_eq mem_type_simps(3) size_of_def)
    apply (simp add: size_of_tag)
    proof safe 
      fix k
      assume "k < size_td (typ_uinfo_t TYPE('a))"
      with `size_of TYPE('a) \<le> unat size_bytes` have "k < unat size_bytes" unfolding size_of_def by unat_arith
      with blocks_size have "k < unat ?node_size * 8" by (simp add: shiftr3_is_div_8, unat_arith)
      hence "ptr_val (ptr_coerce (node +\<^sub>p 1)) + of_nat k \<in> {ptr_val (node +\<^sub>p 1)..+unat ?node_size * 8}"
        by (simp add: intvlI)     
      thus "snd (hrs_htd (t_hrs_' s) (ptr_val (ptr_coerce (node +\<^sub>p 1)) + of_nat k)) = Map.empty"
        using empty by simp
    qed
    next    
      from aligned have "is_aligned (ptr_val (node) + 1 * 2 ^ ALIGN_BITS) ALIGN_BITS"
        by (fastforce intro!: is_aligned_add_multI)
      hence "is_aligned (ptr_val (ptr_coerce (node +\<^sub>p 1) :: 'a ptr)) ALIGN_BITS"
        by (simp add: ptr_add_def)
      with align show "ptr_aligned (ptr_coerce (node +\<^sub>p 1) :: 'a ptr)"
        unfolding is_aligned_def ptr_aligned_def using dvd_trans by blast
    next
      have range_size_subsumes_range_'a: "{ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+size_of TYPE('a)}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat size_bytes}"
            by (simp add: intvl_start_le n) 
      have "(2::nat) ^ len_of (TYPE(32)) = 2 ^ 32" by simp
      have "(size_bytes >> 3) + 1 \<le> ?node_size" using blocks_size by simp
      moreover have "unat (8::word32) = 8" by simp
      moreover have "(8:: word32) > 0" by simp
      ultimately have "((size_bytes >> 3) + 1) * 8 \<le> ?node_size * 8" 
        using `unat ?node_size * 8 < 2 ^ len_of (TYPE(32))`
        apply (simp only: `(2::nat) ^ len_of (TYPE(32)) = 2 ^ 32`)
        using w_mult_pres_le  by presburger
      moreover have "((size_bytes >> 3) + 1) * 8 = (size_bytes >> 3) * 8 + 8"  by unat_arith
      have "unat size_bytes + 8 < 2 ^ 32" sorry
      moreover have "size_bytes < size_bytes + 8"
        using calculation unat_of_nat32 word_bits_conv word_less_nat_alt by fastforce 
      moreover have "(size_bytes >> 3) * 8 + 8 \<ge> size_bytes" 
        apply (simp add: shiftr3_is_div_8) apply (rule l10)
        using \<open>unat (8::32 word) = (8::nat)\<close> calculation(2) apply linarith 
        by simp      
      (* moreover have "unat (ptr_val node) + unat (?node_size * 8) < 2 ^ len_of (TYPE(32))" 
        using node_size by simp  *)
      ultimately have "size_bytes \<le> ?node_size * 8" by auto 
      (* moreover have "unat (ptr_val node) + unat (size_bytes) < 2 ^ len_of (TYPE(32))" sorry *)
      hence "{ptr_val (ptr_coerce (node +\<^sub>p 1))..+unat size_bytes}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p 1))..+ unat (?node_size * 8)}"
        by (simp add: intvl_start_le word_le_nat_alt)
      hence "{ptr_val (ptr_coerce (node +\<^sub>p 1))..+size_of TYPE('a)}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat (?node_size * 8)}"  
        using range_size_subsumes_range_'a by auto   
      hence "0 \<notin> {ptr_val ((ptr_coerce (node +\<^sub>p 1)) :: 'a ptr)..+ size_of TYPE('a)}"
        using zero_not_in_node_range by fast
      thus "c_null_guard (ptr_coerce (node +\<^sub>p 1):: 'a ptr)"
        unfolding c_null_guard_def by blast  
    qed
qed

function trivialxx:: "nat \<Rightarrow> bool"
where "trivialxx n = (True \<or> trivialxx (Suc n))"
by pat_completeness auto
termination
apply size_change

value "Wellfounded.accp {(1::nat,2),(2,3)}"
value "trivialxx_rel 0 1"

apply (relation "measure (\<lambda> (s,heap,n). unat (ptr_val n) - unat (ptr_val heap))")


lemma alloc'_hoare:
fixes size_bytes :: "32 word"
assumes align: "align_of TYPE('a) dvd (2 ^ ALIGN_BITS)"
    and n: "size_of TYPE('a) \<le> unat size_bytes" and "0 < size_bytes"
shows "\<lbrace>\<lambda>s. heap_invs s heap\<rbrace> alloc' heap size_bytes
       \<lbrace>\<lambda>r s. let ptr = (ptr_coerce r) :: ('a :: mem_type) ptr in
        ptr_val r \<noteq> 0 \<longrightarrow> heap_ptr_valid (ptr_retyp ptr (hrs_htd (t_hrs_' s))) ptr\<rbrace>"
unfolding alloc'_def Let_def 
apply (simp add: h_val_field_from_bytes)
apply (subst whileLoop_add_inv 
       [where I="\<lambda> (n,r) s. heap_invs s heap  \<and> reachable s (ptr_coerce heap) n
                  \<and> (r=0 \<longrightarrow> n = NULL \<or> ((size_bytes >> 3) + 1
                     \<le> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast (~~ MEM_NODE_OCCUPIED_FLAG))
                  \<and> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast MEM_NODE_OCCUPIED_FLAG = 0)" 
        and M="\<lambda> ((n,y),s). ptr_val n"])
apply (wp fail'_wp)
apply (simp add: `0 < size_bytes` h_val_id not_le)
defer defer
apply (wp fail'_wp)
apply (auto)
apply (rule self_reachable,solves simp)
apply (drule heap_invs_not_null, solves auto)
apply (rule self_reachable, solves auto)
apply (drule mask_sw32_eq_0_eq_x, solves auto)
apply (drule heap_invs_not_null, solves auto)
apply (drule reachable_trans,solves auto, solves auto)+
apply (drule mask_sw32_eq_0_eq_x, solves auto)
apply (drule reachable_trans,solves auto, solves auto)+
apply (drule mask_sw32_eq_0_eq_x, solves auto)
apply (drule reachable_trans,solves auto, solves auto)

using n align apply (rule alloc'_hoare_helper, auto)
using n align apply (rule alloc'_hoare_helper, auto) 
done
               
       (* and node_size: "node +\<^sub>p uint ?node_size = ?heap_ptr +\<^sub>p 1023"
             and size: "?node_size < HEAP_SIZE" *)
             (* and aligned: "is_aligned (ptr_val (node)) ALIGN_BITS" *)
   (*  unfolding heap_invs_def Let_def sorry *)
  from blocks_size have blocksp1_size: "?blocks + 1 \<le> ?node_size" by unat_arith
  (* from blocks_size and size have blocks_bound: "?blocks < HEAP_SIZE - 1" by unat_arith *)
  (* from  node and  heap_guard_set_array_addrs  have "c_guard node" sorry *) 
  (* from node *) obtain i where i: "node = ?heap_ptr +\<^sub>p (int i)"(*  and "i < HEAP_SIZE" *)
    using array_addrs_ptr_ex sorry
  (* with node_size have heap_i: "heap_ptr +\<^sub>p (int i + uint ?node_size) = heap_ptr +\<^sub>p 1023"
    unfolding ptr_add_def by simp *)
  (* moreover have "(?heap_ptr +\<^sub>p (int i + uint ?node_size) = ?heap_ptr +\<^sub>p 1023)
                  = (int i + uint ?node_size = 1023)" 
    apply (rule ptr_arith_index) using size and `i < HEAP_SIZE`
    apply auto
    apply uint_arith
    done*)
  (* ultimately  have i_size: "int i + uint ?node_size = 1023" by auto *)
  from `i < 1024` have "int i < 1024" by auto
  moreover from size have "uint ?node_size < 1024" by uint_arith
  ultimately have i_blocks: "int i + uint (?blocks + 1) < HEAP_SIZE" using i_size and blocksp1_size
    by (simp, uint_arith)
  hence "heap_ptr +\<^sub>p (int i + uint (?blocks + 1)) \<in> set (array_addrs heap_ptr HEAP_SIZE)" by auto
  with i have new_node_in_heap: "node_' s +\<^sub>p uint (?blocks + 1) \<in> set (array_addrs heap_ptr HEAP_SIZE)"
    unfolding ptr_add_def by (simp add: semiring_normalization_rules(25))
  from i_blocks have "i + unat (?blocks + 1) < HEAP_SIZE"
    by (simp add: uint_nat)
  moreover
  { from blocks_bound have "unat (n >> 3) + unat (2 :: 32 word) < 2 ^ len_of TYPE(32)"
      by (simp add: shiftr3_is_div_8, unat_arith)
    hence "unat ((n >> 3) + 2) = unat (n >> 3) + unat (2 :: 32 word)"
      using unat_add_lem by blast }
  ultimately have i_blocks_u: "i + unat (n >> 3) + unat (2 :: 32 word) < HEAP_SIZE"
    by (simp, unat_arith)
  show "heap_ptr_valid (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) ?ptrc"
  unfolding heap_ptr_valid_def c_guard_def
  proof safe
    show "valid_simple_footprint (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) (ptr_val ?ptrc)
          (typ_uinfo_t TYPE('a))"
    apply (rule TypHeapSimple.valid_simple_footprint_ptr_retyp) defer
    apply (simp, metis Suc_le_eq mem_type_simps(3) size_of_def)
    apply (simp add: size_of_tag)
    proof clarify
      fix k :: nat
      assume "k < size_td (typ_uinfo_t TYPE('a))"
      with n have "k < unat n" by (simp add: size_of_def)
      with blocks_size have "k < unat ?node_size * 8" by (simp add: shiftr3_is_div_8, unat_arith)
      with empty show "snd (hrs_htd (t_hrs_' s) (ptr_val ?ptrc + of_nat k)) = Map.empty"
        using intvlI by (simp, blast)
    qed
  next
    from aligned have "is_aligned (ptr_val (node_' s) + 1 * 2 ^ ALIGN_BITS) ALIGN_BITS"
      by (fastforce intro!: is_aligned_add_multI)
    hence "is_aligned (ptr_val (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)) ALIGN_BITS"
      by (simp add: ptr_add_def)
    with align show "ptr_aligned (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)"
      unfolding is_aligned_def ptr_aligned_def using dvd_trans by blast
  next
    from heap_non_null have "0 \<notin> {ptr_val heap_ptr..+(HEAP_SIZE * size_of TYPE(mem_node_C))}"
      (is "_ \<notin> ?heap") unfolding c_guard_def c_null_guard_def by auto
    moreover have "{ptr_val (node_' s +\<^sub>p 1)..+size_of TYPE('a)} \<subseteq> ?heap" (is "?val \<subseteq> _")
    proof
      fix x
      assume "x \<in> {ptr_val (node_' s +\<^sub>p 1)..+size_of TYPE('a)}" (is "_ \<in> {?start..+?sz}")
      then obtain k where "x = ?start + of_nat k" and "k < ?sz"
        by (blast dest: intvlD)
      with i have x: "x = ptr_val (heap_ptr +\<^sub>p int i +\<^sub>p 1) + of_nat k" by auto
      from `k < ?sz` and n have "k < unat n" by auto
      hence k: "k + 1 < unat ?blocks * 8" by (simp add: shiftr3_is_div_8, unat_arith)
      from i_blocks_u have "8 * i + unat n < 8176" by (simp add: shiftr3_is_div_8, unat_arith)
      show "x \<in> {ptr_val heap_ptr..+1024 * size_of TYPE(mem_node_C)}"
      apply (rule intvl_inter_le [where k=0 and ka="(i + 1) * size_of TYPE(mem_node_C) + k"])
      apply auto
      apply (subst x)
      apply (simp add: ptr_add_def)
      using i_blocks_u and k apply (simp add: shiftr3_is_div_8)
      apply unat_arith
      done
    qed
    with heap_non_null show "c_null_guard (ptr_coerce (node_' s +\<^sub>p 1) :: 'a ptr)"
      unfolding c_guard_def c_null_guard_def by auto
  qed
qed

(*declare [[show_types]]
declare [[show_consts]]
declare [[show_sorts]]*)

lemma alloc_w32_safe: "\<lbrace>\<lambda>s. (liftC lift_global_heap heap_invs) s\<rbrace>
                       exec_concrete lift_global_heap (alloc' 4)
      \<lbrace>\<lambda>r s. ptr_val r \<noteq> 0 \<longrightarrow> is_valid_w32 s ((ptr_coerce r) :: (32 word) ptr)\<rbrace>!"
apply (rule validNF)
apply wp
apply (rule hoare_post_imp)
prefer 2
  apply (rule alloc'_hoare[where 'a="32 word"])
  apply (auto simp add: align_of_def Let_def)+
  apply (simp add: lifted_globals_ext_simps(6) simple_lift_def)
using alloc'_hoare[where n=4 and 'a="32 word"] apply (simp add: Let_def
unfolding validNF_def valid_def
apply auto
proof -
  fix s a b
  assume "\<forall>g. lift_global_heap s = lift_global_heap g \<longrightarrow> heap_invs g"
     and "\<forall>g. lift_global_heap b = lift_global_heap g \<longrightarrow> heap_invs g"
  hence "heap_invs s" and "heap_invs b" by auto
oops

end

end