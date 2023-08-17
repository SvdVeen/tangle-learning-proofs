theory TangleLearning
imports Main ParityGames
begin
chapter \<open>Tangle Learning\<close>
section \<open>Tangle Definitions\<close>

context paritygame begin
(** There must be a nicer way to define this using contexts or locales *)
definition p_tangle :: "nat \<Rightarrow> 'v set \<Rightarrow> bool" where
  "p_tangle p U \<equiv> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (prio ` U) \<and> (\<exists>\<sigma>.
   strategy_of (U \<inter> V_player (player_wins_prio p)) \<sigma> \<and> dom \<sigma> = U \<inter> V_player (player_wins_prio p) \<and> ran \<sigma> \<subseteq> U \<and>
   strongly_connected (E \<inter> (((U \<inter> V_opponent (player_wins_prio p)) \<times> U) \<union> E_of_strat \<sigma>)) \<and>
   (\<forall>v \<in> U \<inter> V_player (player_wins_prio p). \<forall>ys. cycle_from_node (E \<inter> (((U \<inter> V_opponent (player_wins_prio p)) \<times> U) \<union> E_of_strat \<sigma>)) v ys
   \<longrightarrow> player_winningP (player_wins_prio p) (top_priority ys)))"

context
  fixes U :: "'v set"
  assumes ne: "U \<noteq> {}"
  assumes ss: "U \<subseteq> V"
begin

(** Now these names are no longer available for future use, so this is not a great way either *)
private abbreviation (input) pU where "pU \<equiv> MAX v \<in> U. prio v"
private abbreviation (input) \<alpha> where "\<alpha> \<equiv> player_wins_prio pU"
private abbreviation (input) U\<^sub>\<alpha> where "U\<^sub>\<alpha> \<equiv> U \<inter> V_player \<alpha>"
private abbreviation (input) U\<^sub>\<beta> where "U\<^sub>\<beta> \<equiv> U \<inter> V_opponent \<alpha>"
private abbreviation (input) E' :: "'v strat \<Rightarrow> 'v dgraph" where
  "E' \<sigma> \<equiv> E \<inter> ((U\<^sub>\<beta> \<times> U) \<union> E_of_strat \<sigma>)"

definition p_tangle' :: "nat \<Rightarrow> bool" where
  "p_tangle' p \<equiv> p = pU \<and> (\<exists>\<sigma>.
   strategy_of U\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = U\<^sub>\<alpha> \<and>  ran \<sigma> \<subseteq> U \<and> strongly_connected (E' \<sigma>) \<and>
   (\<forall>v \<in> U\<^sub>\<alpha>. \<forall>ys. cycle_from_node (E' \<sigma>) v ys \<longrightarrow> player_winningP \<alpha> (top_priority ys)))"

lemma "p_tangle' p \<longleftrightarrow> p_tangle p U"
  unfolding p_tangle_def p_tangle'_def
  using ss ne by blast
end

lemma ind_subgraph_restr: "\<lbrakk>dom \<sigma> \<subseteq> V\<^sub>\<alpha> \<inter> U; ran \<sigma> \<subseteq> U\<rbrakk> \<Longrightarrow> E \<inter> (((U-V\<^sub>\<alpha>) \<times> U) \<union> E_of_strat \<sigma>) = induced_subgraph (U \<inter> V\<^sub>\<alpha>) \<sigma> \<inter> (U\<times>U)"
  apply (subst ind_subgraph_in_V)
  apply safe
  subgoal using E_in_V by blast
  subgoal using E_in_V by blast
  subgoal unfolding E_of_strat_def by blast
  subgoal unfolding E_of_strat_def using ranI by fast
  done

lemma aux: "U \<subseteq> V \<Longrightarrow> U \<inter> V_opponent \<alpha> = U - V_player \<alpha>"
  using V\<^sub>1_def by (cases \<alpha>) auto

(** It is easier for us to work with induced subgraphs, so we want to show that the original definition is equivalent to one that uses those instead *)
lemma "p_tangle p U \<longleftrightarrow> U \<noteq> {} \<and> U \<subseteq> V \<and> p = Max (prio ` U) \<and> (\<exists>\<sigma>.
  strategy_of (U \<inter>  V_player (player_wins_prio p)) \<sigma> \<and> dom \<sigma> =  U \<inter> V_player (player_wins_prio p) \<and> ran \<sigma> \<subseteq> U \<and>
  strongly_connected (induced_subgraph (U \<inter> V_player (player_wins_prio p)) \<sigma> \<inter> (U\<times>U)) \<and>
  (\<forall>v \<in> U \<inter> V_player (player_wins_prio p). \<forall>ys. cycle_from_node (induced_subgraph (U \<inter> V_player (player_wins_prio p)) \<sigma> \<inter> (U\<times>U)) v ys
  \<longrightarrow> player_winningP (player_wins_prio p) (top_priority ys)))"
  using ind_subgraph_restr[of _ "V_player (player_wins_prio p)" U] aux[of U "player_wins_prio p"]
  unfolding p_tangle_def player_wins_prio_def strategy_of_def
  apply (cases "even p"; simp) by metis+
end
end
