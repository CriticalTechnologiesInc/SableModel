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
  
abbreviation node_size
  where "node_size s n \<equiv> size_C (h_val (hrs_mem (t_hrs_' s)) n)"
abbreviation node_size_masked
  where "node_size_masked s n \<equiv> (node_size s n) && scast (~~ MEM_NODE_OCCUPIED_FLAG)"

abbreviation node_next
where "node_next s n \<equiv> next_C (h_val (hrs_mem (t_hrs_' s)) n)" 
abbreviation node_is_occupied
  where "node_is_occupied s n \<equiv> (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) n)) && scast  MEM_NODE_OCCUPIED_FLAG"
    
abbreviation update_node :: " globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C \<Rightarrow> globals"
where "update_node s n node_val \<equiv>
  (t_hrs_'_update (hrs_mem_update (heap_update n node_val)) s)"
value t_hrs_'_update

abbreviation hrs_the_same_at
where "hrs_the_same_at s s' p \<equiv>
  fst (t_hrs_' s) p = fst (t_hrs_' s') p \<and> snd (t_hrs_' s) p = snd (t_hrs_' s') p"
lemma t_hrs_'_t_hrs_'_update_simp:
  "t_hrs_' (t_hrs_'_update m (s::globals)) = m (t_hrs_' s)" by simp
  
definition nodeFree :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "nodeFree s node \<equiv>
    (let size = (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) node)) && scast (~~ MEM_NODE_OCCUPIED_FLAG) in
    \<forall>p \<in> {ptr_val (node +\<^sub>p 1)..+unat size * size_of TYPE(mem_node_C)}.
      snd (hrs_htd (t_hrs_' s) p) = Map.empty)"
    
definition nodeValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "nodeValid s node = 
  (let occupied = (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) node)) && scast  MEM_NODE_OCCUPIED_FLAG in
   let next = (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) node)) in
   let size = (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) node)) && scast (~~ MEM_NODE_OCCUPIED_FLAG) in
   c_guard node \<and> 
   unat (ptr_val (node +\<^sub>p 1)) + unat (size * 8) \<le> 
    ( if (next \<noteq> NULL) then unat (ptr_val next) else 2 ^ LENGTH(32)) \<and>
   unat (size) * 8 < 2 ^ LENGTH(32) \<and>
   (occupied = 0 \<longrightarrow> nodeFree s node) \<and> 
   (next \<noteq> NULL \<longrightarrow> next > node \<and> next \<ge> (node +\<^sub>p 1)) )"

lemma nodeValid_node_size_l1:
  "nodeValid s node \<Longrightarrow>  unat (ptr_val (node +\<^sub>p 1)) + unat ((node_size_masked s node) * 8) \<le> 
    (2 ^ LENGTH(32))"
  unfolding nodeValid_def Let_def
  apply (subgoal_tac "unat (ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node))) < 2 ^ 32")
   apply (auto simp:if_split)[1]
  by (metis unat_lt2p word_bits_conv word_bits_len_of)   
    
function nodesValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "nodesValid s heap =
  (let next = (node_next s heap) in 
    nodeValid s heap \<and> (next \<noteq> NULL \<longrightarrow> nodesValid s (node_next s heap)))"
by pat_completeness auto

lemma nodesValid_def' :"nodesValid s heap =
  (let next = (mem_node_C.next_C (h_val (hrs_mem (t_hrs_' s)) heap)) in 
    nodeValid s heap \<and> (next \<noteq> NULL \<longrightarrow> nodesValid s next))"
sorry

definition heap_invs :: "globals \<Rightarrow> unit ptr \<Rightarrow> bool"
where
  "heap_invs s heap \<equiv> nodesValid s (ptr_coerce heap)"

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
where "reachable' s node to = (let next = (node_next s node) in
      if node = NULL then to = NULL 
      else node = to \<or> (ptr_val next > ptr_val node \<and> reachable' s next to))"
by pat_completeness auto
termination apply (relation "measure (\<lambda> (s,heap,n). unat (ptr_val n) - unat (ptr_val heap))")
apply auto
sorry

function reachable :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
where "reachable s heap n = (heap \<noteq> NULL \<and>
      (heap = n \<or> 
       (\<exists> n'. n = (node_next s n') \<and>
          ptr_val n > ptr_val n' \<and> reachable s heap n')))"
by pat_completeness auto
termination apply (relation "measure (\<lambda> (s,heap,n). unat (ptr_val n))")
apply auto
  oops

function path :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr list"
  where "path s node to =  
        (if node \<noteq> NULL \<and> 
            ptr_val (node_next s node) > ptr_val node \<and> 
            ptr_val node < ptr_val to \<and>
            ptr_val (node_next s node) \<le> ptr_val to 
         then node # (path s (node_next s node) to) 
         else [])"
by pat_completeness auto
termination sorry

function pathIncl :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr list"
  where "pathIncl s node to =  
        (if node = to then [node]
         else if node \<noteq> NULL \<and> 
            ptr_val (node_next s node) > ptr_val node \<and> 
            ptr_val node < ptr_val to \<and>
            ptr_val (node_next s node) \<le> ptr_val to 
          then node # (pathIncl s (node_next s node) to) 
          else [])"
by pat_completeness auto
termination sorry    

 
fun pathReachable :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
  where "pathReachable s from to =
          (to \<in> set (pathIncl s from to) )"
    
lemma updated_node_hrs_the_same_elsewhere_correct:
  assumes x_val:"x \<notin> ptr_span p"
  shows"hrs_the_same_at s (update_node s p new_node) x" 
sorry
  
lemma updated_node_hrs_the_same_elsewhere_incorrect :
  assumes x_val:"x \<ge> ptr_val (p +\<^sub>p 1) \<or> x < ptr_val p"
  shows"hrs_the_same_at s (update_node s p new_node) x" 
proof-
  let ?xptr = "(Ptr x)::8 word ptr"
  have x[simp] : "ptr_val ?xptr = x" by simp
  hence "ptr_val ?xptr \<ge> ptr_val (p +\<^sub>p 1) \<or> ptr_val ?xptr < ptr_val p" sorry
  {assume "ptr_val ?xptr \<ge> ptr_val (p +\<^sub>p 1)"
    hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}" 
      unfolding intvl_def apply simp unfolding ptr_add_def apply simp  sorry
  }
    {assume "ptr_val ?xptr < ptr_val p"
    hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}" 
      unfolding intvl_def apply simp unfolding ptr_add_def   sorry
  }
     hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}" sorry (* oops *)
  hence "\<forall> h. h_val (heap_update p new_node h) ?xptr = h_val h ?xptr" 
    using h_val_update_regions_disjoint by blast
  hence "\<forall> h. (heap_update p new_node h)  x =  h x" 
    unfolding h_val_def
    apply (simp)
    by(simp add: from_bytes_eq)  
  thus "hrs_the_same_at s (update_node s p new_node) x"
    apply (simp add:t_hrs_'_t_hrs_'_update_simp)
    unfolding hrs_mem_update_def
    apply(simp split:prod.split)
    done
qed
thm t_hrs_'_update_def
thm t_hrs_'_def

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

lemma path_not_empty_node_cond: "set (path s node to) \<noteq> {} \<Longrightarrow> 
        node \<noteq> NULL \<and>
        ptr_val node < ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node)) \<and>
        ptr_val node < ptr_val to \<and> ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node)) \<le> ptr_val to"
using path.simps  by force

lemma p_in_path_not_in_next_eq : 
  assumes p_in_path: "p \<in> set (path s node to)" 
      and p_not_in_next: "p \<notin> set (path s (node_next s node) to)" 
  shows "p = node"
proof-
  from p_in_path have " (path s node to) = node # (path s (node_next s node) to)"
    by (metis emptyE empty_set path.elims)
  with p_in_path have "p \<in>  set (node # (path s (node_next s node) to))" by argo
  hence "p \<in> {node} \<union> set ((path s (node_next s node) to))" by (metis insert_is_Un list.simps(15)) 
  with p_not_in_next have " p \<in> {node}" by blast
  thus "p = node" by simp
qed
    
lemma p_in_path_l_to:  
  shows " p \<in> set (path s node to ) \<longrightarrow> p < to"
  apply (rule_tac ?P = "\<lambda> s node to. p \<in> set (path s node to ) \<longrightarrow> p < to" in path.induct)
proof clarify
  fix s node to
  assume ih: "(node \<noteq> NULL \<and>
        ptr_val node < ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node)) \<and>
        ptr_val node < ptr_val to \<and> ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node)) \<le> ptr_val to \<Longrightarrow>
        p \<in> set (path s (next_C (h_val (hrs_mem (t_hrs_' s)) node)) to) \<longrightarrow> p < to)"
    and p: "p \<in> set (path s node to)"
  from p have 1:"node \<noteq> NULL \<and>
        ptr_val node < ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node)) \<and>
        ptr_val node < ptr_val to \<and> ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node)) \<le> ptr_val to" 
    using path_not_empty_node_cond by (metis emptyE) 
  with ih have 2:"p \<in> set (path s (next_C (h_val (hrs_mem (t_hrs_' s)) node)) to) \<longrightarrow> p < to" by blast
  { assume "p \<in> set (path s (next_C (h_val (hrs_mem (t_hrs_' s)) node)) to)"
    hence "p < to" using 2 by blast
  } moreover 
  { assume "p \<notin> set (path s (next_C (h_val (hrs_mem (t_hrs_' s)) node)) to)"
    with p have " p = node" using p_in_path_not_in_next_eq by presburger
    hence "ptr_val p < ptr_val to" using 1 by blast
    hence "p < to"  by (simp add: ptr_less_def ptr_less_def')
  } ultimately show "p < to" by blast
qed
  
lemma p_in_path_ge_node : "p \<in> set (path s node to) \<Longrightarrow>  p \<ge>  node"
  sorry
lemma p_in_path_next_le_to : "p \<in> set (path s node to) \<Longrightarrow> (node_next s p) \<le> to"
  sorry

lemma hrs_the_same_nodes_the_same:
  "\<forall>p \<in> {ptr_val (node::mem_node_C ptr)..+size_of (TYPE(mem_node_C))}. hrs_the_same_at s s' p \<Longrightarrow>
    (h_val (hrs_mem (t_hrs_' s)) node) = (h_val (hrs_mem (t_hrs_' s')) node)"
  unfolding h_val_def hrs_mem_def
  apply (subgoal_tac " heap_list (fst (t_hrs_' s)) (size_of TYPE(mem_node_C)) (ptr_val node) =
     heap_list (fst (t_hrs_' s')) (size_of TYPE(mem_node_C)) (ptr_val node)")
   apply auto
  apply (rule heap_list_h_eq2)
  by simp
     
lemma heaps_eq_imp_paths_eq:
  "\<forall> p . p \<ge> ptr_val fst_node \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at  s s' p
       \<Longrightarrow>  path s fst_node to = path s' fst_node to" 
apply (induction rule:path.induct)  
  sorry
    
lemma hrs_the_same_imp_nodeValid:
  "\<forall>p \<in> {ptr_val node ..+ size_of (TYPE(mem_node_C))}. hrs_the_same_at s s' p \<Longrightarrow>
   \<forall>p \<in> {ptr_val (node +\<^sub>p 1) ..+ unat (node_size_masked s node) * size_of TYPE(mem_node_C)}. hrs_the_same_at s s' p \<Longrightarrow>   
   nodeValid s node \<Longrightarrow> 
   nodeValid s' node"
  unfolding nodeValid_def nodeFree_def Let_def
  apply (subgoal_tac "node_next s node = node_next s' node")
   apply (subgoal_tac "node_size s node = node_size s' node")
    apply(frule hrs_the_same_nodes_the_same)
    apply clarsimp
    apply (simp add:hrs_htd_def )
    apply auto[1]
   apply (frule hrs_the_same_nodes_the_same) apply auto[1]
  apply (frule hrs_the_same_nodes_the_same) apply auto[1]
  done
    
lemma nodeValid_imp_range_l:"ptr_val n < ptr_val to \<Longrightarrow> nodeValid s n \<Longrightarrow> nodeValid s to \<Longrightarrow> 
      \<forall> p \<in>{ptr_val n ..+ size_of (TYPE(mem_node_C))}. p < ptr_val to"
  sorry
    
lemma "nodesValid s heap \<Longrightarrow>
       \<forall> p . p \<ge> ptr_val heap \<and> p < ptr_val (last_node +\<^sub>p 1) \<longrightarrow>  hrs_the_same_at s s' p
       \<Longrightarrow> \<forall> n \<in> set (path s heap last_node). nodeValid s' n"
  sorry
      
lemma self_reachable: "n \<noteq> NULL \<Longrightarrow> reachable s n n"
sorry

lemma reachable_trans :
  "reachable s heap n \<Longrightarrow> n \<noteq> NULL \<Longrightarrow> reachable s heap (node_next s n)" 
  sorry
    
lemma nodesValid_trans_back: "nodeValid s node \<Longrightarrow> 
    nodesValid s next \<Longrightarrow> 
    node_next s node = next \<Longrightarrow>
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
  
thm word_mult_le_mono1

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

(* declare [[show_types]]  *)
(* declare [[show_sorts]] *)
(* declare [[show_consts]] *)
thm alloc'_def
thm nodeValid_def
print_record globals

lemma nodesValid_not_null:
  "nodesValid s heap \<Longrightarrow> heap \<noteq> NULL"
  by (meson c_guard_NULL_simp nodeValid_def nodesValid_def') 
    
lemma hrs_the_sam_nodesValid_reachable_imp_reachable:
  assumes "reachable s heap node"
    and "nodesValid s heap"
    and "\<forall>p . p \<ge> ptr_val heap \<and> p < ptr_val node \<longrightarrow> hrs_the_same_at s s' p"
  shows "reachable s' heap node" 
  sorry

lemma node_in_path_nodesValid_imp_nodeValid_node:
  assumes "n \<in> set (path s fst_node to)" 
    and "nodesValid s fst_node"
  shows "nodeValid s n" 
  sorry
    
lemma nodesValid_reachable_imp_in_path: 
  assumes "nodesValid s fst_node" 
  and "reachable s fst_node a"
  shows  "fst_node \<in> set (path s fst_node a)"
  sorry
    
lemma nodesValid_l1:
assumes "nodesValid s node" 
    and "nodeValid s' node"
    and "c_guard (node +\<^sub>p 1)"
    and "\<forall>x. x \<ge> ptr_val (node +\<^sub>p 1) \<longrightarrow> hrs_the_same_at s s' x"
shows "nodesValid s' node"
sorry

lemma nodesValid_l2:
      "nodeValid s heap \<Longrightarrow>
       \<forall> p \<in> set (path s heap node). nodeValid s p \<Longrightarrow>
       reachable s heap node \<Longrightarrow>
       nodesValid s node \<Longrightarrow>
       nodesValid s heap"
  sorry
    
lemma nodesValid_l3:
  "nodeValid s node \<Longrightarrow>
   node_next s node = NULL \<Longrightarrow>
    nodesValid s node"
  by (meson nodesValid_def')

function test_termination
  where "test_termination (x::nat) = (if (x > 100) then 1 else test_termination (x + 1))"
by (pat_completeness, auto)
termination 
apply (relation "measure (\<lambda> (x). 100 - x)") apply simp 
sorry
  
lemma c_guard_l1:
  assumes "c_guard (a::('a::mem_type) ptr)"
  "\<not> c_guard (a +\<^sub>p 1)"
  "b > a" 
  "b \<ge> a +\<^sub>p 1"
shows "\<not> c_null_guard b" 
proof -
  have "\<not> c_null_guard ( a +\<^sub>p 1)" using `c_guard a` `\<not> c_guard (a +\<^sub>p 1)`
    unfolding c_guard_def apply auto    
    apply(frule ptr_aligned_plus[where i = 1]) by auto
  hence "0 \<in> ptr_span (a +\<^sub>p 1)" unfolding c_null_guard_def by auto
  have "0 \<in> ptr_span b" using `b \<ge> a +\<^sub>p 1` using `0 \<in> ptr_span (a +\<^sub>p 1)` unfolding intvl_def
  proof simp
    assume "a +\<^sub>p 1 \<le> b"
       and "\<exists>k. ptr_val (a +\<^sub>p 1) + of_nat k = 0 \<and> k < size_of TYPE('a)"
    then obtain k where k:"ptr_val (a +\<^sub>p 1) + of_nat k = 0 \<and> k < size_of TYPE('a)" by auto
    hence "ptr_val (a +\<^sub>p 1) + of_nat k = 0" by auto
    {
      assume "((of_nat k)::32 word) \<noteq> 0"
      have "ptr_val b \<ge> ptr_val (a +\<^sub>p 1)" using `b \<ge> a +\<^sub>p 1`  by (simp add: ptr_le_def ptr_le_def')
      hence 1:"ptr_val b - ptr_val (a +\<^sub>p 1) \<le> of_nat k" 
        using `ptr_val (a +\<^sub>p 1) + of_nat k = 0`
        apply unat_arith apply auto
        using `of_nat k \<noteq> 0` 
        apply (subgoal_tac "unat ((of_nat k)::32 word) = 0 \<Longrightarrow> ((of_nat k)::32 word) = 0")
         apply auto[1]
        apply (subst (asm) (3) unat_eq_0)  by auto
          
      let ?k2' = "of_nat k - ( ptr_val b - ptr_val (a +\<^sub>p 1))"
      have "ptr_val b + ?k2' = of_nat k + ptr_val (a +\<^sub>p 1)" by simp
      hence "ptr_val b + ?k2' = 0" using k by (simp add: add.commute)
      hence 2:"ptr_val b + of_nat (unat ?k2') = 0" by simp
          
      let ?of_nat_k = "((of_nat k):: 32 word)"
      have "?k2' \<le> ?of_nat_k" using 1  word_sub_le by auto
      hence "unat ?k2' \<le> unat ?of_nat_k" by (simp add: word_le_nat_alt) 
      moreover have "unat ?of_nat_k \<le> k" by (metis le_cases le_unat_uoi) 
      moreover  have "k < size_of TYPE('a)" using k by simp
      ultimately have "(unat ?k2') < size_of TYPE('a)" by simp
      hence "ptr_val b + of_nat (unat ?k2') = 0 \<and> (unat ?k2') < size_of TYPE('a)" using 2 by simp
      hence "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)" by (frule exI)
    }
    moreover{  
      assume k_eq_0:"((of_nat k)::32 word) = 0" 
      let ?k2' = "of_nat (size_of TYPE('a)) - ( ptr_val b - ptr_val a)"
      have "ptr_val b > ptr_val a" using `b>a` 
        by (simp add: ptr_less_def ptr_less_def')
      hence "unat (ptr_val b) > unat (ptr_val a)" using unat_mono by auto
      from k_eq_0 have "ptr_val (a +\<^sub>p 1)= 0" using k by unat_arith
      hence 1:"ptr_val a + of_nat (size_of TYPE('a)) = 0" unfolding ptr_add_def by simp
      hence 2: "ptr_val b - ptr_val a < of_nat (size_of TYPE('a))" 
        using k_eq_0
        apply unat_arith apply auto
         apply (subgoal_tac "unat (ptr_val a) \<noteq> (0::nat)")
          apply auto[1]
        using `c_guard a` 
         apply (metis len_of_addr_card max_size mem_type_simps(3) neq0_conv unat_of_nat_len)
        using `unat (ptr_val b) > unat (ptr_val a)` by simp
      hence "ptr_val b + ?k2' = 0" using 1  by (simp add: add.commute)
      hence 3:"ptr_val b + of_nat (unat ?k2') = 0" by simp
      have "ptr_val b - ptr_val a > 0" using `ptr_val b > ptr_val a` 
        using word_neq_0_conv by fastforce 
      with 2 have "?k2' < of_nat (size_of TYPE('a))"  by unat_arith 
      hence "unat ?k2' < size_of TYPE('a)" using unat_less_helper by auto
      with 3 have "ptr_val b + of_nat (unat ?k2') = 0 \<and> unat ?k2' < size_of TYPE('a)" by auto
      hence "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)" by (frule exI)  
    }
    ultimately show "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)"
      by auto
  qed 
  thus "\<not> c_null_guard b" unfolding c_null_guard_def by auto
qed
  
lemma eight_eq_eight : "unat (8::32 word) = 8" by simp
lemma one_mask_neg_MNOF_not_zero[simp]:
  "(1::32 signed word) && ~~ MEM_NODE_OCCUPIED_FLAG = (0::32 signed word) \<Longrightarrow> False"
     unfolding MEM_NODE_OCCUPIED_FLAG_def by unat_arith
lemma self_impl: "Q \<Longrightarrow> Q" by auto


lemma alloc'_invs:
  fixes size_bytes:: "32 word" and heap:: "unit ptr"
  assumes size_bytes_g0 : "size_bytes > 0"
  shows "\<lbrace>\<lambda>s. heap_invs s heap \<rbrace> (alloc' heap size_bytes) \<lbrace> \<lambda>r s. heap_invs s heap \<rbrace>"
  unfolding alloc'_def Let_def 
  apply (simp add: h_val_field_from_bytes)
  apply (subst whileLoop_add_inv 
      [where I="\<lambda> (n,r) s. heap_invs s heap \<and> reachable s (ptr_coerce heap) n
                  \<and> (r=0 \<longrightarrow> (n = NULL \<or> ((size_bytes >> 3) + 1
                        \<le> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast (~~ MEM_NODE_OCCUPIED_FLAG))
                     \<and> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast MEM_NODE_OCCUPIED_FLAG = 0))" 
        and M="\<lambda> ((n,y),s). ptr_val n"])
  apply (wp )
      prefer 5
      apply (rule_tac Q="heap_invs s heap" in self_impl, simp)
     prefer 4
     apply (simp add: size_bytes_g0)
     apply (rule return_wp)
    apply auto
                    apply (drule c_guard_NULL,drule reachable_trans, auto)+ 
                 defer
                 apply (drule c_guard_NULL,drule reachable_trans, solves auto, solves auto)+
               defer 
               apply (drule c_guard_NULL,drule reachable_trans, auto) 
              defer
              apply (drule c_guard_NULL,drule reachable_trans,auto)+
            apply (drule one_mask_neg_MNOF_not_zero, auto)
           apply (drule c_guard_NULL,drule reachable_trans, auto)+
         apply (frule mask_sw32_eq_0_eq_x, solves simp)
        apply (drule c_guard_NULL,drule reachable_trans, auto)
       defer
       defer
       defer
       apply (drule one_mask_neg_MNOF_not_zero, auto)
      apply (frule mask_sw32_eq_0_eq_x, solves simp)
     apply (drule c_guard_NULL,drule reachable_trans, auto)
    prefer 3
    apply (wp, auto)
           apply (rule self_reachable, simp)
          apply (drule heap_invs_not_null, simp)
         apply (rule self_reachable, simp)
        apply (drule one_mask_neg_MNOF_not_zero, auto)
       apply (drule heap_invs_not_null, simp)
      apply (rule self_reachable, simp)
     apply (frule mask_sw32_eq_0_eq_x, solves simp)
    apply (drule heap_invs_not_null, simp)
proof -
  fix a::"mem_node_C ptr"
  fix s::globals
  assume invs: "heap_invs s heap"
    and node_free :"node_size s a && scast MEM_NODE_OCCUPIED_FLAG = 0"
    and reachable: "reachable s (ptr_coerce heap) a"
    and "a \<noteq> NULL"
    and "c_guard a"
    (* and "c_guard (a +\<^sub>p uint (2 + (size_bytes >> 3))) " *)
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
  moreover have "node_next ?new_s a \<noteq> NULL \<longrightarrow> a < node_next ?new_s a \<and> a+\<^sub>p1 \<le> node_next ?new_s a"
    using  `nodeValid s a`
    apply (subst `node_next ?new_s a = node_next s a`)+ by (meson nodeValid_def)     
  ultimately have "nodeValid ?new_s a" unfolding nodeValid_def by presburger 
  moreover have hrs_the_same_after_a:
    "c_guard (a +\<^sub>p 1) \<Longrightarrow> \<forall> x. x \<ge> ptr_val (a +\<^sub>p 1) \<longrightarrow> hrs_the_same_at s ?new_s x"
    using updated_node_hrs_the_same_elsewhere_incorrect by simp
  {
   assume "c_guard (a +\<^sub>p 1)"  
   hence "nodesValid ?new_s a" 
     using `nodesValid s a` `nodeValid ?new_s a` hrs_the_same_after_a nodesValid_l1 by blast
  } moreover {
    assume "\<not> c_guard (a +\<^sub>p 1)"       
    {
      assume "node_next s a \<noteq> NULL" 
      have "(node_next s a) > a" 
        using `nodeValid s a` `node_next s a \<noteq> NULL` unfolding nodeValid_def by metis
      moreover have "(node_next s a) \<ge> (a +\<^sub>p 1)" 
        using `nodeValid s a` `node_next s a \<noteq> NULL` unfolding nodeValid_def by metis
      ultimately have "\<not> c_null_guard (node_next s a)" 
        using `c_guard a` `\<not> c_guard (a +\<^sub>p 1)` 
        apply (rule_tac a=a and b="(node_next s a)" in c_guard_l1) by auto
      from `nodesValid s a` `node_next s a \<noteq> NULL` have "nodeValid s (node_next s a)"
        using nodesValid_def' unfolding nodeValid_def by metis
      hence "c_guard (node_next s a)" unfolding nodeValid_def by meson
      with `\<not> c_null_guard (node_next s a)` have False unfolding c_guard_def by auto
    }
    hence "node_next s a = NULL" by auto
    hence "node_next ?new_s a = NULL" using `node_next ?new_s a = node_next s a` by auto
    hence "nodesValid ?new_s a" using `nodeValid ?new_s a` nodesValid_l3 by blast
    }
    ultimately have "nodesValid ?new_s a"  by blast 
    moreover have hrs_the_same_before_a: "\<forall> p. p< ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p" sorry
    hence hrs_the_same_heap_to_a:"\<forall>p. p\<ge> ptr_val (ptr_coerce heap) \<and> p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p"
      by blast
  moreover have "\<forall> p \<in> set (path ?new_s (ptr_coerce heap) a). nodeValid ?new_s p" 
    sorry
  moreover have "reachable ?new_s (ptr_coerce heap) a" 
     
    sorry
  moreover have "nodeValid ?new_s (ptr_coerce heap)"
    sorry
  ultimately have "nodesValid ?new_s (ptr_coerce heap)" using nodesValid_l2 by blast
  thus "heap_invs ?new_s heap" unfolding heap_invs_def by blast
next 
  fix a::"mem_node_C ptr"
  fix s::globals
  let ?node_size_masked = "node_size s a && scast (~~ MEM_NODE_OCCUPIED_FLAG)"
  let ?new_size =  "((size_bytes >> (3::nat)) + (1::32 word) || scast MEM_NODE_OCCUPIED_FLAG)"
  let ?new_size_masked = "?new_size && scast (~~ MEM_NODE_OCCUPIED_FLAG)"
  let ?new_next = "a +\<^sub>p uint ( 2 + (size_bytes >>3) )"
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
  assume "heap_invs s heap"
    "reachable s (ptr_coerce heap) a"
    "(size_bytes >> 3) + 1  \<le> ?node_size_masked"
    "node_size s a && scast MEM_NODE_OCCUPIED_FLAG = 0"
    "(size_bytes >> 3) + 1  < ?node_size_masked"
    "c_guard a"
    "a \<noteq> NULL"
    "c_guard ?new_next"
  have "nodesValid s (ptr_coerce heap)" using `heap_invs s heap` unfolding heap_invs_def by auto
  hence "a \<ge> (ptr_coerce heap)" using `reachable s (ptr_coerce heap) a` sorry 
  have "(1::int) + uint (1 + (size_bytes >>3)) < 2 ^ LENGTH(32)" sorry     
  hence "uint (2 + (size_bytes >>3) ) =  1 + uint (1 + (size_bytes >>3))" by uint_arith
  hence "ptr_val a + of_int( (uint (2 + (size_bytes >>3) )) * xx) = 
         ptr_val a + of_int( (1 + uint ((size_bytes >>3) + 1)) * xx)" by simp 
  hence "a +\<^sub>p uint ( 2 + (size_bytes >>3) ) = (a +\<^sub>p 1) +\<^sub>p uint ((size_bytes >>3)+ 1)" 
    unfolding ptr_add_def by simp 
      
  have "?new_next \<noteq> NULL" using `c_guard ?new_next` c_guard_NULL by auto
  have "nodeValid s a" using `heap_invs s heap` `reachable s (ptr_coerce heap) a` `a \<noteq> NULL`
    by (rule invs_reachable_imp_valid)
  have size_mem_node_c[simp]:"size_of (TYPE(mem_node_C)) = 8" by simp 
  have new_s_simp[simp]: "?new_s_simp = ?new_s" by simp
  have new_size[simp]: "node_size ?new_s a= ?new_size " by (metis new_s_simp updated_node_size)
  have new_next[simp]: "node_next ?new_s a= ?new_next " by (metis new_s_simp updated_node_next)
  have "nodeValid ?new_s ?new_next" unfolding nodeValid_def sorry  
  hence "nodesValid ?new_s ?new_next" sorry
  have "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)" 
    using `nodeValid s a` unfolding nodeValid_def by meson
  have node_size_masked_l_2p32:"(unat ?node_size_masked) * unat (8::32 word) < (2::nat) ^ len_of (TYPE(32))" 
    using `nodeValid s a` unfolding nodeValid_def apply(subst eight_eq_eight) by metis
  hence "((size_bytes >> 3) + 1) * 8 < ?node_size_masked * 8"
    using `(size_bytes >> 3) + 1  < ?node_size_masked`
    by (metis eight_eq_eight unat_0 word_gt_0_no word_mult_less_mono1 zero_neq_numeral)          
  moreover have "unat (ptr_val (a+\<^sub>p1)) + unat (?node_size_masked * 8) \<le> (2::nat) ^ len_of (TYPE(32))"
    using `nodeValid s a` nodeValid_node_size_l1 by fast 
  ultimately have "unat (ptr_val (a+\<^sub>p1)) + unat ( ((size_bytes >>3) +1) * 8) < (2::nat) ^ len_of (TYPE(32))"
    using `(size_bytes >>3) +1 < ?node_size_masked` `unat ?node_size_masked * 8 < 2 ^ LENGTH(32)`
    by unat_arith
  moreover have "unat (ptr_val (a+\<^sub>p1)) + unat ( ((size_bytes >>3) +1) * 8) = 
          unat (ptr_val ((a+\<^sub>p1) +\<^sub>p uint (1 + (size_bytes >> 3))))" 
    using calculation
    apply (simp)
    apply(subgoal_tac "unat (ptr_val (a +\<^sub>p 1)) + unat ((size_bytes >> 3) * 8 + 8) =
       unat (ptr_val (a +\<^sub>p 1) +( (size_bytes >> 3) * 8 + 8))" )
     apply(simp)
    unfolding ptr_add_def
    by (unat_arith, rule unat_add_lem'[THEN sym], auto)
  {      
      have "unat (ptr_val(a +\<^sub>p 1)) + unat (((size_bytes >>3)+ 1) * 8) < 2 ^ LENGTH(32)"
        using `(size_bytes >> 3) + 1  < ?node_size_masked` 
          \<open>unat (ptr_val (a +\<^sub>p 1)) + unat (?node_size_masked * 8) \<le> 2 ^ LENGTH(32)\<close>
        by (metis \<open>unat (ptr_val (a +\<^sub>p 1)) + unat (((size_bytes >> 3) + 1) * 8) = unat (ptr_val (a +\<^sub>p 1 +\<^sub>p uint (1 + (size_bytes >> 3))))\<close> unat_lt2p)
      hence "ptr_val(a +\<^sub>p 1) + ((size_bytes >>3)+ 1) * 8  \<ge> ptr_val(a +\<^sub>p 1)"
        using no_olen_add_nat by blast
          
      moreover have "(a +\<^sub>p 1) +\<^sub>p uint ((size_bytes >>3)+ 1) = (a +\<^sub>p 1) +\<^sub>p unat ((size_bytes >>3)+ 1)"
        by (simp add: uint_nat)
          
      ultimately have "ptr_val ?new_next \<ge>  ptr_val (a +\<^sub>p 1)"
        using `?new_next = (a +\<^sub>p 1) +\<^sub>p uint ((size_bytes >>3)+ 1)` unfolding ptr_add_def
        by (metis (mono_tags, hide_lams) mem_node_C_size of_int_uint of_nat_numeral ptr_val.ptr_val_def) 
      hence "?new_next \<ge> (a +\<^sub>p 1)" by (simp add: ptr_le_def ptr_le_def') 
      moreover have "(a +\<^sub>p 1) > a" sorry
      ultimately have new_next_g_a:"?new_next > a \<and> ?new_next \<ge> (a +\<^sub>p 1)" using order_less_le_trans by auto 
    } note  new_next_g_a= this
  moreover{
    have "((size_bytes >> 3) + 1) && scast MEM_NODE_OCCUPIED_FLAG = 0"
      unfolding MEM_NODE_OCCUPIED_FLAG_def sorry (* obvious *)
    hence new_size_eq:"?new_size_masked = (size_bytes >> 3) + 1"
      by (simp add: sable_isa.l11 sable_isa.mask_sw32_eq_0_eq_x)
    have 1:"unat (ptr_val (a +\<^sub>p 1)) + unat (?node_size_masked * 8) 
      \<le> (if ?next \<noteq> NULL then unat (ptr_val ?next) else (2::nat) ^ LENGTH(32))" 
      using `nodeValid s a` unfolding nodeValid_def Let_def by simp
        (* have "unat (((size_bytes >> 3) + 1) * 8) < unat (?node_size_masked * 8)"
      using `(size_bytes >> 3) + 1  < ?node_size_masked`  sorry *)
        (*hence 2: "unat (ptr_val (a +\<^sub>p 1)) + unat (((size_bytes >> 3) + 1) * 8) \<le>
          unat (ptr_val (a +\<^sub>p 1)) + unat (?node_size_masked * 8)"
      using add_le_cancel_left nat_less_le sorry by blast *)
        (*from 1 and 2 have "unat (ptr_val (a +\<^sub>p 1)) + unat (((size_bytes >> 3) + 1) * 8)
       \<le> (if ?next \<noteq> NULL then unat (ptr_val ?next) else (2::nat) ^ LENGTH(32))"
      using le_trans by blast *)
        (*hence "unat (ptr_val (a +\<^sub>p 1)) + unat (?new_size_masked * 8)
       \<le> (if ?next \<noteq> NULL then unat (ptr_val ?next) else (2::nat) ^ LENGTH(32))"
      by (simp add:new_size_eq)*)
        

    moreover have "unat (ptr_val ((a+\<^sub>p1) +\<^sub>p uint (1 + (size_bytes >> 3)))) =
           unat (ptr_val (a +\<^sub>p uint (2 + (size_bytes >> 3))))"
      by (simp add: \<open>a +\<^sub>p uint (2 + (size_bytes >> 3)) = a +\<^sub>p 1 +\<^sub>p uint ((size_bytes >> 3) + 1)\<close> add.commute) 
      (* \<up> duplicate fact? \<up> *)
    ultimately have "unat (ptr_val (a +\<^sub>p 1)) + unat (?new_size_masked * 8)
       \<le> (if ?new_next \<noteq> NULL then unat (ptr_val ?new_next) else (2::nat) ^ LENGTH(32))"
      using  new_size_eq `?new_next = (a +\<^sub>p 1) +\<^sub>p uint ((size_bytes >>3)+ 1)`
      `unat (ptr_val (a+\<^sub>p1)) + unat ( ((size_bytes >>3) +1) * 8) < (2::nat) ^ len_of (TYPE(32))`
      \<open>unat (ptr_val (a +\<^sub>p 1)) + unat (((size_bytes >> 3) + 1) * 8) = unat (ptr_val (a +\<^sub>p 1 +\<^sub>p uint (1 + (size_bytes >> 3))))\<close> 
      by auto       
    moreover{ have "(unat ?node_size_masked) * 8 < 2 ^ LENGTH(32)" 
        using `nodeValid s a` unfolding nodeValid_def by meson  
      with `(size_bytes >> 3) + 1  < ?node_size_masked` 
      have "(unat ?new_size_masked) * 8 < 2 ^ LENGTH(32)"
        apply (subst new_size_eq) apply(drule unat_mono)  by linarith
    }
    moreover{
      have "node_is_occupied ?new_s a = scast MEM_NODE_OCCUPIED_FLAG"
        by (metis (no_types) new_s_simp sable_isa.updated_node_size word_ao_absorbs(5))
      hence "node_is_occupied ?new_s a \<noteq> 0" unfolding MEM_NODE_OCCUPIED_FLAG_def by auto 
    }
    moreover  have "(?new_next \<noteq> NULL \<longrightarrow> ?new_next > a \<and> ?new_next \<ge> a +\<^sub>p 1)" using new_next_g_a by auto
    ultimately have "nodeValid ?new_s a" using `c_guard a` unfolding nodeValid_def
      using new_next new_size by auto        
  }      
  ultimately have "nodesValid ?new_s a" using nodesValid_trans_back new_next
    using `nodesValid ?new_s ?new_next` by blast
      (* have "unat (ptr_val (a +\<^sub>p 1)) + unat (?node_size_masked * 8) \<le> unat (ptr_val ?next)" 
    using `nodeValid s a` unfolding nodeValid_def  
    by (simp add: `?next \<noteq> NULL`) *)
  have "\<forall> p. p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s_simp p"
    apply clarify
    apply (rule updated_node_blahblah_2) using new_next_g_a 
    apply (subgoal_tac "ptr_val a < ptr_val ( a +\<^sub>p uint (2 + (size_bytes >> 3)))")
    by (auto simp:ptr_less_def' ptr_less_def)
  hence range_imp_hrs_the_same:
    "\<forall> p. p \<ge> ptr_val (ptr_coerce heap) \<and> p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s_simp p"
    by simp
      
  hence paths_the_same:"path s (ptr_coerce heap) a = path ?new_s (ptr_coerce heap) a"
    apply (subst new_s_simp[THEN sym]) 
    by (rule heaps_eq_imp_paths_eq)
      
  have new_s_path_nodeValid:"\<forall> p \<in> set (path ?new_s (ptr_coerce heap) a). nodeValid ?new_s p"
  proof clarify
    fix np::"mem_node_C ptr"
    assume np_in_path:"np \<in> set (path ?new_s (ptr_coerce heap) a)"
    have "ptr_val np < ptr_val a" 
      using np_in_path p_in_path_l_to ptr_less_def ptr_less_def' by blast
    moreover have "ptr_val np \<ge> ptr_val (ptr_coerce heap)" 
      using np_in_path p_in_path_ge_node ptr_le_def ptr_le_def'
      by (metis Ptr_ptr_coerce ptr_val.ptr_val_def)        
    ultimately have "hrs_the_same_at s ?new_s (ptr_val np)" using range_imp_hrs_the_same
      by simp    
        
    have np_in_s_path:"np \<in> set (path s (ptr_coerce heap) a)" using np_in_path  paths_the_same by argo    
    hence "nodeValid s np" using `nodesValid s (ptr_coerce heap)` 
      node_in_path_nodesValid_imp_nodeValid_node by fast
    
    have "node_next s np \<le> a" using np_in_s_path  p_in_path_next_le_to by blast
    with `nodeValid s np` have "unat (ptr_val (np +\<^sub>p 1)) + unat((node_size_masked s np) * 8) \<le> 
    ( if (node_next s np \<noteq> NULL) then unat (ptr_val (node_next s np)) else 2 ^ LENGTH(32))"
      unfolding nodeValid_def by metis
    moreover have "node_next s np \<noteq> NULL"
      by (metis (no_types) \<open>nodeValid s np\<close> Ptr_not_null_pointer_not_zero Ptr_ptr_coerce  c_guard_NULL nodeValid_def ptr_coerce_NULL reachable_def' reachable_trans word_not_simps(1))
      (* \<up> suspicious \<up> *)
    ultimately have "unat (ptr_val (np +\<^sub>p 1)) + unat((node_size_masked s np) * 8) \<le> 
      unat (ptr_val (node_next s np))" by auto
    hence "unat (ptr_val (np +\<^sub>p 1)) + unat((node_size_masked s np) * 8) \<le> unat (ptr_val a)"
      using `node_next s np \<le> a`
      apply (simp  add: ptr_le_def ptr_le_def')
      by unat_arith
    moreover have "unat (node_size_masked s np) * 8 < 2 ^ LENGTH(32)" using `nodeValid s np` 
      unfolding nodeValid_def by metis
    ultimately have "\<forall>p \<in> {ptr_val (np +\<^sub>p 1)..+unat (node_size_masked s np) * size_of TYPE(mem_node_C)}. 
     p < ptr_val a"     
      unfolding intvl_def
      apply unat_arith  apply auto
      apply (subgoal_tac "unat (node_size_masked s np) * 8 < 2 ^ LENGTH(32)")
       apply (subgoal_tac "unat (of_nat k) = k") 
        apply(subgoal_tac "unat (node_size_masked s np) * 8 = unat ((node_size_masked s np) * 8)")
         apply (erule_tac t="unat (of_nat k)" in ssubst) 
         apply simp
        apply (metis sable_isa.eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
       apply (simp add: unat_of_nat_eq)
      by simp
    hence "\<forall>p \<in> {ptr_val (np +\<^sub>p 1)..+unat (node_size_masked s np) * size_of TYPE(mem_node_C)} .
           hrs_the_same_at s ?new_s p" 
      by (simp add:`\<forall> p <ptr_val a. hrs_the_same_at s ?new_s_simp p`)  
    from `nodeValid s np` have "\<forall> p \<in> {ptr_val np ..+ size_of (TYPE(mem_node_C))}. p < ptr_val a"
      using `ptr_val np < ptr_val a`
        `nodeValid s a` nodeValid_imp_range_l by blast
    hence "\<forall>p \<in> {ptr_val np ..+ size_of (TYPE(mem_node_C))}. hrs_the_same_at s ?new_s p"
      by (simp add:`\<forall> p <ptr_val a. hrs_the_same_at s ?new_s_simp p`)
    moreover have "\<forall>p\<in>{ptr_val (np +\<^sub>p 1) ..+ unat (node_size_masked s np) * size_of TYPE(mem_node_C)}.
       hrs_the_same_at s ?new_s p" sorry (* not a matter of convincing Isabelle  *)
    ultimately show "nodeValid ?new_s np" using `nodeValid s np` hrs_the_same_imp_nodeValid by blast  
  qed     
      
  moreover have "reachable ?new_s (ptr_coerce heap) a"
    apply (subst new_s_simp[THEN sym])
    using `reachable s (ptr_coerce heap) a`
      `nodesValid s (ptr_coerce heap)`
      range_imp_hrs_the_same
      hrs_the_sam_nodesValid_reachable_imp_reachable by blast
      
  moreover{    
    {assume "a > ptr_coerce heap" 
      hence "(ptr_coerce heap) \<in> set (path s (ptr_coerce heap) a)" 
        using `nodesValid s (ptr_coerce heap)` `reachable s (ptr_coerce heap) a` 
        nodesValid_reachable_imp_in_path by fast
      hence "(ptr_coerce heap) \<in> set (path ?new_s (ptr_coerce heap) a)"
        using paths_the_same by argo
      hence  "nodeValid ?new_s (ptr_coerce heap)" using new_s_path_nodeValid by fast
    }
    moreover
    {assume "\<not>a > ptr_coerce heap"
      hence "a = ptr_coerce heap" using ` a \<ge>  ( ptr_coerce heap)` by simp
      hence "nodeValid ?new_s (ptr_coerce heap)" using `nodeValid ?new_s a` by simp
    }
    ultimately have "nodeValid ?new_s (ptr_coerce heap)" by blast
  }
  ultimately have "nodesValid ?new_s (ptr_coerce heap)" using
      `nodesValid ?new_s a` apply (simp only:`?new_s_simp = ?new_s`[THEN sym]) 
    apply (rule nodesValid_l2) by blast+ 
  thus "heap_invs ?new_s heap" unfolding heap_invs_def by auto
qed
 
lemma alloc'_hoare_helper:
  fixes size_bytes heap
  assumes n:"size_of TYPE('a) \<le> unat size_bytes"
    and align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)"
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
  assume "ptr_val (node +\<^sub>p 1) \<noteq> 0" 
    and invs: "heap_invs s heap"
    and blocks_size: "?blocks \<le> ?node_size"
    and "reachable s (ptr_coerce heap) node"
    and node_empty: "size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast MEM_NODE_OCCUPIED_FLAG = 0"
    and "node \<noteq> NULL"
    and "c_guard node"
    and "ptr_val (node +\<^sub>p 1) \<noteq> 0"
  have "nodeValid s node"  using `reachable s (ptr_coerce heap) node` \<open>node \<noteq> NULL\<close>
    using invs invs_reachable_imp_valid by blast
  hence nodeFree:"nodeFree s node" using node_empty unfolding nodeValid_def by meson 
  hence empty: "\<forall>p\<in>{ptr_val (node +\<^sub>p 1)..+unat ?node_size * 8}.
                            snd (hrs_htd (t_hrs_' s) p) = Map.empty"
    unfolding nodeFree_def by auto
  have node_size: "unat (ptr_val (node +\<^sub>p 1)) + unat (?node_size * 8) \<le> 2 ^ len_of (TYPE(32))"
    using `nodeValid s node`  sable_isa.nodeValid_node_size_l1 by presburger   
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
  hence zero_not_in_node_range:"0 \<notin> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat (?node_size * 8)}" 
    by simp
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
      with `size_of TYPE('a) \<le> unat size_bytes` have "k < unat size_bytes" 
        unfolding size_of_def by unat_arith
      with blocks_size have "k < unat ?node_size * 8" by (simp add: shiftr3_is_div_8, unat_arith)
      hence "ptr_val (ptr_coerce (node +\<^sub>p 1)) + of_nat k \<in> {ptr_val (node +\<^sub>p 1)..+unat ?node_size * 8}"
        by (simp add: intvlI)     
      thus "snd (hrs_htd (t_hrs_' s) (ptr_val (ptr_coerce (node +\<^sub>p 1)) + of_nat k)) = Map.empty"
        using empty by simp
    qed
  next    
    show "ptr_aligned (ptr_coerce (node +\<^sub>p 1) :: 'a ptr)"
      using align `c_guard node` unfolding c_guard_def
      by (metis gcd_nat.trans ptr_aligned_def ptr_aligned_plus ptr_val_ptr_coerce) 
  next
    have range_size_subsumes_range_'a: 
      "{ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+size_of TYPE('a)}
      \<subseteq>{ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat size_bytes}"
      by (simp add: intvl_start_le n) 
    have "(2::nat) ^ len_of (TYPE(32)) = 2 ^ 32" by simp
    have "(size_bytes >> 3) + 1 \<le> ?node_size" using blocks_size by simp
    moreover have "unat (8::word32) = 8" by simp
    moreover have "(8:: word32) > 0" by simp
    ultimately have "((size_bytes >> 3) + 1) * 8 \<le> ?node_size * 8" 
      using `unat ?node_size * 8 < 2 ^ len_of (TYPE(32))` word_mult_le_mono1 by fastforce 
    moreover have "((size_bytes >> 3) + 1) * 8 = (size_bytes >> 3) * 8 + 8"  by unat_arith
    have "unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)"
      using `(size_bytes >> 3) + 1 \<le> ?node_size` `nodeValid s node` 
      unfolding nodeValid_def Let_def by (simp add: le_def word_le_nat_alt) 
    hence "unat size_bytes + 8 < 2 ^ 32" by (simp add: shiftr3_is_div_8 ) unat_arith 
    moreover have "size_bytes < size_bytes + 8"
      using calculation unat_of_nat32 word_bits_conv word_less_nat_alt by fastforce 
    moreover have "(size_bytes >> 3) * 8 + 8 \<ge> size_bytes" 
      apply (simp add: shiftr3_is_div_8) apply (rule l10)
      using \<open>unat (8::32 word) = (8::nat)\<close> calculation(2) by linarith simp      
    ultimately have "size_bytes \<le> ?node_size * 8" by auto 
    hence "{ptr_val (ptr_coerce (node +\<^sub>p 1))..+unat size_bytes}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p 1))..+ unat (?node_size * 8)}"
      by (simp add: intvl_start_le word_le_nat_alt)
    hence "{ptr_val (ptr_coerce (node +\<^sub>p 1))..+size_of TYPE('a)}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat (?node_size * 8)}"  
      using range_size_subsumes_range_'a by auto   
    hence "0 \<notin> {ptr_val ((ptr_coerce (node +\<^sub>p 1)) :: 'a ptr)..+ size_of TYPE('a)}"
      using zero_not_in_node_range by fast
    thus "c_null_guard (ptr_coerce (node +\<^sub>p 1):: 'a ptr)" unfolding c_null_guard_def by blast  
  qed
qed

function trivialxx:: "nat \<Rightarrow> bool"
where "trivialxx n = (True \<or> trivialxx (Suc n))"
by pat_completeness auto
termination
sorry

value "trivialxx_rel 0 1"

thm iffD1[OF refl]
  
lemma alloc'_hoare:
  fixes size_bytes :: "32 word"
  assumes align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)"
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
     prefer 2
     apply (erule iffD1[OF refl])
    apply (auto simp: `0 < size_bytes`)
                    apply wp
                    apply auto
                      apply (rule self_reachable, solves simp)
                      apply (drule heap_invs_not_null, solves auto)
                      apply (rule self_reachable, solves auto)
                      apply (drule one_mask_neg_MNOF_not_zero, solves simp)
                      apply (drule heap_invs_not_null, solves auto)
                      apply (rule self_reachable, solves auto)
                     apply (drule mask_sw32_eq_0_eq_x, solves auto)
                    apply (drule heap_invs_not_null, solves auto)
                   apply (drule reachable_trans,solves auto, solves auto)+
                apply (drule one_mask_neg_MNOF_not_zero, solves simp)
               apply (drule reachable_trans,solves auto, solves auto)
              apply (drule c_guard_NULL,rule reachable_trans, solves simp, solves simp)
             apply (drule mask_sw32_eq_0_eq_x, solves auto)
            apply (drule c_guard_NULL,drule reachable_trans, solves simp, solves simp)+
        apply (drule one_mask_neg_MNOF_not_zero, solves simp)
       apply (drule c_guard_NULL,drule reachable_trans, solves simp, solves simp)+
     apply (drule mask_sw32_eq_0_eq_x, solves auto)
    apply (drule c_guard_NULL,drule reachable_trans, solves simp, solves simp)
  using n align apply (rule alloc'_hoare_helper, auto)
  using n align apply (rule alloc'_hoare_helper, auto) 
  done
    
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