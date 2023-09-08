theory TangleLearning
imports Main ParityGames
begin
chapter \<open>Tangle Learning\<close>
section \<open>Tangle Definitions\<close>

context paritygame begin

(** As defined by Van Dijk:
    A p-tangle is a nonempty set of vertices U \<subseteq> V with p = pr(U),
    for which player \<alpha> \<equiv>\<^sub>2 p has a strategy \<sigma>: U\<^sub>\<alpha> \<rightarrow> U, such that the graph (U,E'),
    with E' := E \<inter> (\<sigma> \<union> (U\<^sub>\<beta> \<times> U)), is strongly connected and player \<alpha> wins all cycles in (U,E').*)
definition p_tangle :: "nat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "p_tangle p U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (pr ` U) \<and>
  (let \<alpha> = player_wins_pr p in (
    \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
  ))))"

definition tangle :: "'v set \<Rightarrow> bool" where
  "tangle U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and>
  (let \<alpha> = player_wins_pr (pr_set U) in (
    \<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
    (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
      strongly_connected E' \<and>
      (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
  ))))"

lemma tangle_notempty[simp]: "\<not>tangle {}"
  unfolding tangle_def by simp

lemma tangle_in_V: "tangle U \<Longrightarrow> U \<subseteq> V"
  unfolding tangle_def by simp

lemma closed_tangle_is_winning_region:
  assumes tangle: "tangle U"
  assumes closed_opp: "\<forall>u \<in> U. u \<in> V_opponent (player_wins_pr(pr_set U)) \<longrightarrow> E `` {u} \<subseteq> U"
  shows "winning_region (player_wins_pr (pr_set U)) U"
proof -
  from tangle have U_in_V: "U \<subseteq> V" using tangle_in_V by simp

  let ?\<alpha> = "player_wins_pr (pr_set U)"
  from tangle obtain \<sigma> where
      \<sigma>_strat: "strategy_of_player ?\<alpha> \<sigma>"
  and \<sigma>_dom: "dom \<sigma> = U \<inter> V_player ?\<alpha>"
  and \<sigma>_ran: "ran \<sigma> \<subseteq> U"
  and \<sigma>_conn: "strongly_connected (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
  and \<sigma>_winning: "\<forall>v\<in>U. \<forall>xs. cycle_node (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U)) v xs
    \<longrightarrow> player_wins_list ?\<alpha> xs"
    unfolding tangle_def Let_def by auto

  from \<sigma>_dom closed_opp have \<sigma>_subgraph_closed: "induced_subgraph (dom \<sigma>) \<sigma> `` U \<subseteq> U"
    using ind_subgraph_closed_region[OF U_in_V _ \<sigma>_ran, of "dom \<sigma>"]
    using V_opponent_player_int[OF U_in_V, of ?\<alpha>]
    by blast

  have \<sigma>_winning': "\<forall>u\<in>U. \<forall>ys. cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) u ys
        \<longrightarrow> player_wins_list (player_wins_pr (pr_set U)) ys"
  proof (rule ballI; rule allI; rule impI)
    fix u ys
    assume u_in_U: "u \<in> U" and cycle_u_ys: "cycle_from_node (induced_subgraph (dom \<sigma>) \<sigma>) u ys"
    from cycle_from_node_closed_set[OF u_in_U \<sigma>_subgraph_closed cycle_u_ys]
    have ys_in_U: "set ys \<subseteq> U" .

      from cycle_u_ys ys_in_U obtain y where
          cycle_y_ys: "cycle_node (induced_subgraph (dom \<sigma>) \<sigma>) y ys"
      and y_in_U: "y \<in> U"
        unfolding cycle_from_node_def
        using origin_in_cycle_node by fastforce

      have "induced_subgraph (dom \<sigma>) \<sigma> \<inter> (U\<times>U) \<subseteq> (E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent ?\<alpha>) \<times> U))"
        apply (subst \<sigma>_dom; simp; rule conjI)
        subgoal using ind_subgraph[of "U \<inter> V_player ?\<alpha>"] by blast
        subgoal apply (subst V_opponent_player_int[OF U_in_V])
          unfolding induced_subgraph_def by fast
        done
      from \<sigma>_winning y_in_U subgraph_cycle[OF this cycle_restr_V[OF cycle_y_ys ys_in_U]]
      show "player_wins_list ?\<alpha> ys" by simp
  qed

  show "winning_region ?\<alpha> U"
    apply (simp add: winning_region_strat tangle_in_V[OF tangle])
    apply (rule exI[where x="\<sigma>"]; intro conjI)
    subgoal using \<sigma>_strat .
    subgoal using \<sigma>_dom Int_commute ..
    subgoal using \<sigma>_ran .
    subgoal using \<sigma>_winning' .
    subgoal using closed_opp .
    done
qed

definition player_tangle :: "player \<Rightarrow> 'v set \<Rightarrow> bool" where
  "player_tangle \<alpha> U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> \<alpha> = player_wins_pr (pr_set U) \<and>
  (\<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = U \<inter> V_player \<alpha> \<and> ran \<sigma> \<subseteq> U \<and>
  (let E' = E \<inter> (E_of_strat \<sigma> \<union> (U \<inter> V_opponent \<alpha>) \<times> U) in (
    strongly_connected E' \<and>
    (\<forall>v \<in> U. \<forall>xs. cycle_node E' v xs \<longrightarrow> player_wins_list \<alpha> xs)
  )))"

lemma player_tangle_equiv_tangle: "tangle U \<longleftrightarrow> player_tangle (player_wins_pr (pr_set U)) U"
  unfolding tangle_def player_tangle_def Let_def by simp

(** lemma ind_subgraph_int: "\<lbrakk>dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> U; ran \<sigma> \<subseteq> U\<rbrakk>
  \<Longrightarrow> E \<inter> (((U-V\<^sub>\<alpha>) \<times> U) \<union> E_of_strat \<sigma>) = induced_subgraph (U \<inter> V\<^sub>\<alpha>) \<sigma> \<inter> (U\<times>U)"
  apply (subst ind_subgraph_in_V)
  apply safe
  subgoal using E_in_V by blast
  subgoal using E_in_V by blast
  subgoal unfolding E_of_strat_def by blast
  subgoal unfolding E_of_strat_def using ranI by fast
  done *)

(** I may want to move these definitions into a player_paritygame context like the original attractor definition *)
definition escapes :: "player \<Rightarrow> 'v set \<Rightarrow> 'v set" where
  "escapes \<alpha> t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V_opponent \<alpha> \<and> v \<in> V - t}"
end

context player_paritygame
begin

definition opponent_escapes :: "'v set \<Rightarrow> 'v set" where
  "opponent_escapes t \<equiv> {v. \<exists>u. (u,v) \<in> E \<and> u \<in> t \<inter> V\<^sub>\<beta> \<and> v \<in> V - t}"

abbreviation V\<^sub>\<alpha>_player where "V\<^sub>\<alpha>_player \<equiv> if V\<^sub>\<alpha> = V\<^sub>0 then EVEN else ODD"

context
  fixes T :: "'v set set"
  assumes T_tangles : "\<forall>t\<in>T. player_tangle V\<^sub>\<alpha>_player t"
begin

inductive_set player_tangle_attractor :: "'v set \<Rightarrow> 'v set" for A where
  base: "x \<in> A \<Longrightarrow> x \<in> player_tangle_attractor A"
| own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-A; (x,y) \<in> E; y \<in> player_tangle_attractor A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor A"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y) \<in> E \<longrightarrow> y \<in> player_tangle_attractor A\<rbrakk>
              \<Longrightarrow> x \<in> player_tangle_attractor A"
| escape: "\<lbrakk>x \<in> t-A; t \<in> T; opponent_escapes t \<noteq> {};
            \<forall>v. v \<in> opponent_escapes t \<longrightarrow> v \<in> player_tangle_attractor A\<rbrakk>
            \<Longrightarrow> x \<in> player_tangle_attractor A"

lemma target_in_player_tangle_attractor: "A \<subseteq> player_tangle_attractor A"
  using player_tangle_attractor.base by blast

lemma "player_tangle_attractor A \<subseteq> A \<union> V"
  apply auto oops


lemma "A \<noteq> {} \<Longrightarrow> A \<subseteq> V \<Longrightarrow> tangle (player_tangle_attractor A)"
  unfolding tangle_def Let_def
  apply auto
  subgoal using target_in_player_tangle_attractor by auto
  subgoal for x y sorry
  subgoal sorry
end

inductive_set player_tangle_attractor' :: "'v set set \<Rightarrow> 'v set \<Rightarrow> 'v set" for T A where
  base: "x \<in> A \<Longrightarrow> x \<in> player_tangle_attractor' T A"
| own: "\<lbrakk>x \<in> V\<^sub>\<alpha>-A; (x,y)\<in>E; y \<in> player_tangle_attractor' T A\<rbrakk> \<Longrightarrow> x \<in> player_tangle_attractor' T A"
| opponent: "\<lbrakk>x \<in> V\<^sub>\<beta>-A; \<forall>y. (x,y)\<in>E \<longrightarrow> y \<in> player_tangle_attractor' T A\<rbrakk>
              \<Longrightarrow> x \<in> player_tangle_attractor' T A"
| escape: "\<lbrakk>x \<in> t-A; t \<in> T; opponent_escapes t \<noteq> {}; 
             \<forall>e. e \<in> opponent_escapes t \<longrightarrow> e \<in> player_tangle_attractor' T A\<rbrakk>
             \<Longrightarrow> x \<in> player_tangle_attractor' T A"
end

end
