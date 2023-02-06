chapter \<open>Parity Games\<close>
theory ParityGames
imports Main
begin
section \<open>Parity Game Definitions\<close>
subsection \<open>Directed Graphs\<close>
text \<open>
  An arena \<A> in parity games consists of a directed graph and sets of vertices with owners.
  It is defined as \<A> = (V,V0,V1,E) where
  - (V,E) is a directed graph
  - V0 and V1 = V\V0 are sets of vertices belonging to the two players
  - E \<subseteq> V \<times> V is a set of edges, such that every vertex has at least one successor
  The simplest way for us to represent this is as a directed graph of integers (which will be priorities),
  and a set of vertices belonging to player 0.
\<close>
text \<open>A directed graph is represented as a set of edges\<close>
type_synonym 'v dgraph = "('v\<times>'v) set"
definition succs :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "succs E v \<equiv> E``{v}"
definition is_succ :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_succ E v w \<equiv> w \<in> succs E v"

lemma "w \<in> succs E v \<Longrightarrow> is_succ E v w"
  unfolding is_succ_def succs_def by auto

subsection \<open>Paths and Cycles\<close>
context
  fixes E :: "'v dgraph"
begin
  definition V where "V = fst`E \<union> snd`E"

  lemma "finite E \<Longrightarrow> finite V"
  unfolding V_def by simp

  fun path :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
     "path v [] v' \<longleftrightarrow> v = v'"
  |  "path v (x#xs) v' \<longleftrightarrow> (v,x) \<in> E \<and> path x xs v'"

  lemma path_is_rtrancl: "path v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
    apply (induction xs arbitrary: v)
    apply auto by fastforce

  lemma rtrancl_is_path: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path.simps(1) apply blast
    using path.simps(2) by blast

  lemma path_append: "path u xs v \<Longrightarrow> path v ys w \<Longrightarrow> path u (xs@ys) w"
    apply (induction xs arbitrary: u) by auto
    
  lemma path_subset: "path v xs v' \<Longrightarrow> set xs \<subseteq> V"
  unfolding V_def
  proof (induction xs arbitrary: v)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    hence "(v,a) \<in> E" by simp
    hence "a \<in> snd ` E" by force
    with Cons show ?case by auto
  qed

  lemma path_decomp_1: "path u (xs@[v]@ys) w \<Longrightarrow> path u (xs@[v]) v"
    apply (induction xs arbitrary: u) by auto

  lemma path_decomp_2: "path u (xs@[v]@ys@[w]@zs) x \<Longrightarrow> path v (ys@[w]) w"
    apply (induction xs arbitrary: u)
    using path_decomp_1 apply fastforce
    by fastforce

  lemma distinct_length: "distinct xs \<Longrightarrow> length xs = card (set xs)"
    apply (induction xs) by auto

  lemma not_distinct_length: "length xs > card (set xs) \<Longrightarrow> \<not>distinct xs"
    apply (induction xs) by auto

  lemma finite_subset_not_distinct: "finite S \<Longrightarrow> set xs \<subseteq> S \<Longrightarrow> length xs > card S \<Longrightarrow> \<not>distinct xs"
  proof (rule ccontr; simp)
    assume finite: "finite S"
      and subset: "set xs \<subseteq> S"
      and len: "length xs > card S"
      and distinct: "distinct xs"
    hence "card (set xs) = length xs" by (simp add: distinct_length)
    with len have card_gt: "card (set xs) > card S" by simp
    also from subset finite have card_lt_eq: "card (set xs) \<le> card S"
      using card_mono by blast
    finally show "False" by auto
  qed
  
  definition cycle_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_node v xs \<equiv> path v xs v \<and> xs \<noteq> []"

  definition cycle_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_from_node v xs \<equiv> \<exists>v'. (v,v')\<in>E\<^sup>* \<and> cycle_node v' xs"

  lemma lasso_decomp: "path u xs v \<Longrightarrow> cycle_node v ys \<Longrightarrow> cycle_from_node u ys"
    unfolding cycle_from_node_def using path_is_rtrancl by auto

  (* First auxiliary lemma: find a path of any length that holds *)
  lemma path_any_length: "finite E \<Longrightarrow> \<forall>v. E``{v} \<noteq> {} \<Longrightarrow> \<exists>xs v'. length xs = n \<and> path v xs v'"
  proof (induction n)
    case 0
    then obtain xs v' where "xs=([]::'v list)" and "v' = v" by simp
    then show ?case by auto
  next
    case (Suc n)
    then obtain xs v' w
      where path: "length xs = n \<and> path v xs v'"
      and succ: "w \<in> E``{v'}" by fast
    then obtain ys where append: "ys = xs@[w]" by fast
    with path have length: "length ys = Suc n" by simp
    from append path succ have "path v ys w" by (auto simp: path_append)
    with length show ?case by auto
  qed

  (*
   obtain xs v'. length xs = card(V)+1 \<and> path ...
   set xs \<subseteq> V
   distinct xs \<Longrightarrow> length xs = card (set xs)
   length xs > card (set xs) \<Longrightarrow> \<not>distinct xs
   xs = xs1 v xs2 v xs3
  *)

  lemma "finite E \<Longrightarrow> \<forall>v. E``{v} \<noteq> {} \<Longrightarrow> \<exists>x xs. cycle_from_node x xs"
  proof -
    assume fin: "finite E" and succ: "\<forall>v. E``{v} \<noteq> {}"
    then obtain v xs v' where xs: "length (xs::'v list) = (card V) + 1 \<and> path v xs v'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path_subset by auto
      moreover from xs have "length xs > card V" by auto
      moreover from fin have "finite V" unfolding V_def by simp
      ultimately show ?thesis by (simp add: finite_subset_not_distinct)
    qed
    hence "\<exists>x xs1 xs2 xs3. xs = xs1 @ [x] @ xs2 @ [x] @ xs3" using not_distinct_decomp by blast
    then obtain x xs1 xs2 xs3 where decomp: "xs = xs1 @ [x] @ xs2 @ [x] @ xs3" by blast
    with xs have "path v (xs1@[x]) x" using path_decomp_1 by auto
    moreover from decomp xs have "path x (xs2@[x]) x" using path_decomp_2 by auto
    hence "cycle_node x (xs2@[x])" by (simp add: cycle_node_def)
    ultimately have "cycle_from_node v (xs2@[x])" by (simp add: lasso_decomp)
    then show ?thesis by auto
  qed
end

subsection \<open>Paths in Subgraphs\<close>
lemma subgraph_path: "E' \<subseteq> E \<Longrightarrow> path E' v vs v' \<Longrightarrow> path E v vs v'"
  apply (induction vs arbitrary: v) by auto

lemma subgraph_cycle: "E' \<subseteq> E \<Longrightarrow> cycle_node E' v vs \<Longrightarrow> cycle_node E v vs"
  unfolding cycle_node_def
  apply (induction vs arbitrary: v)
  by (auto simp: subgraph_path)

lemma subgraph_lasso: "E' \<subseteq> E \<Longrightarrow> cycle_from_node E' v vs \<Longrightarrow> cycle_from_node E v vs"
  unfolding cycle_from_node_def
  proof (induction vs arbitrary: v)
    case Nil
    then show ?case by (simp add: cycle_node_def)
  next
    case (Cons a vs)
    then obtain v' where v_v'_sub: "(v,v')\<in>E'\<^sup>*"
      and cycle_v'_sub: "cycle_node E' v' (a # vs)" by fast
    from v_v'_sub Cons.prems(1) have v_v': "(v,v')\<in>E\<^sup>*"
      using rtrancl_mono by auto
    from cycle_v'_sub Cons.prems(1) have cycle_v': "cycle_node E v' (a # vs)"
      by (auto simp: subgraph_cycle)
    with v_v' show ?case by auto
  qed

subsection \<open>Winning strategies\<close>

locale arena_defs =
  fixes E :: "'v dgraph"
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
  assumes fin: "finite E"
  assumes succ: "E``{v} \<noteq> {}"
  assumes V\<^sub>0_ss: "V\<^sub>0 \<subseteq> fst`E \<union> snd`E"
begin  
  definition V where "V = fst`E \<union> snd`E"
  definition V\<^sub>1 where "V\<^sub>1 = V-V\<^sub>0"

  lemma players_disjoint: "V\<^sub>0 \<inter> V\<^sub>1 = {}"
    unfolding V_def V\<^sub>1_def by auto

  text \<open>A positional strategy for a player i is a function \<sigma>:Vi\<rightarrow>V\<close>
  type_synonym 'a strat = "'a \<Rightarrow> 'a option"

  definition E_of_strat :: "'a strat \<Rightarrow> 'a dgraph" where
    "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"

  definition top_priority :: "'v list \<Rightarrow> nat" where
    "top_priority xs \<equiv> MAX v \<in> set xs. prio v"

  abbreviation winning_even :: "'v list \<Rightarrow> bool" where
    "winning_even xs \<equiv> even (top_priority xs)"

  abbreviation winning_odd :: "'v list \<Rightarrow> bool" where
    "winning_odd xs \<equiv> odd (top_priority xs)"

  definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S"

  lemma strats_disjoint: "\<forall>\<sigma> \<tau>. strategy_of V\<^sub>0 \<sigma> \<and> strategy_of V\<^sub>1 \<tau> \<longrightarrow> (dom \<sigma> \<inter> dom \<tau>) = {}"
    unfolding strategy_of_def using players_disjoint by blast

  definition induced_by_strategy :: "'v strat \<Rightarrow> 'v dgraph" where
    "induced_by_strategy \<sigma> = E \<inter> ((-dom \<sigma>) \<times> UNIV \<union> E_of_strat \<sigma>)"

  lemma ind_subgraph: "induced_by_strategy \<sigma> \<subseteq> E"
    unfolding induced_by_strategy_def by auto

  lemma ind_subgraph_cycle: "cycle_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_node E v xs"
  proof -
    assume 0: "cycle_node (induced_by_strategy \<sigma>) v xs"
    from ind_subgraph have 1: "induced_by_strategy \<sigma> \<subseteq> E" by simp
    hence "cycle_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_node E v xs"
      by (simp add:subgraph_cycle)
    with 0 1 show ?thesis by simp
  qed

  lemma ind_subgraph_lasso: "cycle_from_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_from_node E v xs"
  proof -
    assume 0: "cycle_from_node (induced_by_strategy \<sigma>) v xs"
    from ind_subgraph have 1: "induced_by_strategy \<sigma> \<subseteq> E" by simp
    hence "cycle_from_node (induced_by_strategy \<sigma>) v xs \<Longrightarrow> cycle_from_node E v xs"
      by (simp add:subgraph_lasso)
    with 0 1 show ?thesis by simp
  qed

  definition won_by_even :: "'v \<Rightarrow> bool" where
    "won_by_even v \<equiv> \<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and> 
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> winning_even xs)"

  lemma "won_by_even v \<Longrightarrow> \<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> \<not>winning_odd xs)"
    unfolding won_by_even_def by auto

  definition won_by_odd :: "'v \<Rightarrow> bool" where
    "won_by_odd v \<equiv> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and> 
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> winning_odd xs)"

  lemma "won_by_odd v \<Longrightarrow> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy \<sigma>) v xs \<longrightarrow> \<not>winning_even xs)"
    unfolding won_by_odd_def by auto

lemma w1: "won_by_even v \<Longrightarrow> \<not>won_by_odd v"
  unfolding won_by_even_def won_by_odd_def sorry

lemma w2:"won_by_even v \<or> won_by_odd v" sorry

lemma "won_by_even v \<noteq> won_by_odd v" using w1 w2 by blast 

end

subsection \<open>Miscellaneous\<close>

text \<open>
  A strategy for player i is a function \<sigma>:V*Vi\<rightarrow>V that selects a successor for every history of the
  play ending in a vertex of player i.
  A strategy is memoryless iff \<sigma>(wv) = \<sigma>(v) for all w\<in>V*, v\<in>Vi.
  A strategy is winning from a vertex v if all plays starting in v and consistent with \<sigma> are winning
  for player i.
\<close>

locale arena = arena_defs E V\<^sub>0 
  for  
    E :: "'v dgraph"
  and V\<^sub>0 :: "'v set"  
  + 
  assumes V0_ss: "V\<^sub>0 \<subseteq> V"
  assumes succ: "E``{v}\<noteq>{}"
  assumes fin: "finite (UNIV::'v set)"
begin

text \<open>Wholly unnecessary but allows me to not have to unfold V1_def all the time.\<close>
lemma V1_ss[simp]: "V\<^sub>1 \<subseteq> V"
  unfolding V\<^sub>1_def by auto

definition connected where "connected v v' \<longleftrightarrow> (v,v')\<in>E\<^sup>*"
  
lemma conn: "v\<in>V \<Longrightarrow> connected v v' \<Longrightarrow> v'\<in>V"
  unfolding connected_def V_def
  by (metis Range.RangeI Range_snd UnCI rtranclE)
end
  
end
