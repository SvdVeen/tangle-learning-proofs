theory WinningRegions
imports Main ParityGames
begin
chapter \<open>Winning Regions\<close>
section \<open>Winning Regions for Arbitrary Players\<close>
context player_paritygame begin
(** Shorthand for who wins a cycle *)
abbreviation "winning_player xs \<equiv> winningP (pr_list xs)"
abbreviation "winning_opponent xs \<equiv> \<not>winningP (pr_list xs)"

(** A winning region is a region in the graph where one player has a strategy that makes it
    closed, and where every cycle reachable from every node in that region is won by that
    player *)
definition player_winning_region :: "'v set \<Rightarrow> bool" where
  "player_winning_region W \<equiv> W\<subseteq>V \<and> (\<exists>\<sigma>.
    strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> = V\<^sub>\<alpha> \<inter> W \<and> ran \<sigma> \<subseteq> W \<and> E `` (W \<inter> V\<^sub>\<beta>) \<subseteq> W \<and>
    (\<forall>v\<in>W. \<forall>xs. reachable_cycle (induced_subgraph \<sigma>) v xs \<longrightarrow> winning_player xs))"

lemma player_winning_region_empty[simp]: "player_winning_region {}"
  unfolding player_winning_region_def strategy_of_def E_of_strat_def
  by auto

(** The winning region exists in the graph *)
lemma player_winning_region_in_V: "player_winning_region W \<Longrightarrow> W\<subseteq>V"
  unfolding player_winning_region_def by simp

(** This definition exists for symmetry *)
definition losing_region :: "'v set \<Rightarrow> bool" where
  "losing_region W \<equiv> W\<subseteq>V \<and> (\<exists>\<sigma>.
    strategy_of V\<^sub>\<beta> \<sigma> \<and> dom \<sigma> = V\<^sub>\<beta> \<inter> W \<and> ran \<sigma> \<subseteq> W \<and> E `` (W\<inter>V\<^sub>\<alpha>) \<subseteq> W \<and>
    (\<forall>v\<in>W. \<forall>xs. reachable_cycle (induced_subgraph \<sigma>) v xs \<longrightarrow> winning_opponent xs))"

lemma losing_region_empty[simp]: "losing_region {}"
  unfolding losing_region_def strategy_of_def E_of_strat_def
  by auto

(** The losing region exists in the graph *)
lemma losing_region_in_V: "losing_region L \<Longrightarrow> L\<subseteq>V"
  unfolding losing_region_def by simp

(** A single node is won by the player if the player has a strategy where all the cycles
    reachable from that node are won by the player *)
definition won_by_player :: "'v \<Rightarrow> bool" where
  "won_by_player v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
   (\<forall>xs. reachable_cycle (induced_subgraph \<sigma>) v xs \<longrightarrow> winning_player xs))"

(** A node that is won by the player is part of the graph *)
lemma won_by_player_in_V: "won_by_player v \<Longrightarrow> v\<in>V"
  unfolding won_by_player_def by simp

(** This definition exists for symmetry *)
definition won_by_opponent :: "'v \<Rightarrow> bool" where
  "won_by_opponent v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>\<beta> \<sigma> \<and>
  (\<forall>xs. reachable_cycle (induced_subgraph \<sigma>) v xs \<longrightarrow> winning_opponent xs))"

(** A vertex that is won by the opponent exists in the graph *)
lemma won_by_opponent_in_V: "won_by_opponent v \<Longrightarrow> v\<in>V"
  unfolding won_by_opponent_def by simp

(** Every node in a winning region for a player is won by that player *)
lemma player_winning_region_won_by_player: "player_winning_region W \<Longrightarrow> \<forall>w\<in>W. won_by_player w"
  unfolding player_winning_region_def won_by_player_def by blast

(** Every node in a losing region for a player is won by their opponent *)
lemma losing_region_won_by_opponent: "losing_region W \<Longrightarrow> \<forall>w\<in>W. won_by_opponent w"
  unfolding losing_region_def won_by_opponent_def by blast

(** If a node is won by the player, it cannot be won by the opponent *)
lemma winning_v_exclusive: "won_by_player v \<Longrightarrow> \<not>won_by_opponent v"
  unfolding won_by_player_def won_by_opponent_def
proof clarsimp
  fix \<sigma> \<sigma>'
  define G\<sigma> where "G\<sigma> = induced_subgraph \<sigma>"
  define G\<sigma>' where "G\<sigma>' = induced_subgraph \<sigma>'"
  assume \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
    and \<sigma>_win: "\<forall>xs. reachable_cycle G\<sigma> v xs \<longrightarrow> winningP (pr_list xs)"
    and \<sigma>'_opp: "strategy_of (V-V\<^sub>\<alpha>) \<sigma>'"
    and "v\<in>V"
  interpret Ginter: paritygame "G\<sigma> \<inter> G\<sigma>'" V V\<^sub>0 pr
    using ind_subgraph_inter_opposed[OF G\<sigma>_def G\<sigma>'_def \<sigma>_player \<sigma>'_opp] .

  from Ginter.cycle_always_exists[OF \<open>v\<in>V\<close>] Ginter.succ \<open>v\<in>V\<close>
  obtain xs where xs: "reachable_cycle (G\<sigma> \<inter> G\<sigma>') v xs" by blast
  moreover from xs have "reachable_cycle G\<sigma> v xs" using reachable_cycle_inter by fastforce
  with \<sigma>_win have "winningP (pr_list xs)" by blast
  moreover from xs have "reachable_cycle G\<sigma>' v xs" using reachable_cycle_inter by fastforce
  ultimately show "\<exists>xs. reachable_cycle (G\<sigma>') v xs \<and> winning_player xs" by blast
qed

(** By the previous lemma, a node cannot be won by both players at the same time *)
corollary "\<not>(won_by_player v \<and> won_by_opponent v)"
  using winning_v_exclusive by blast

(** If a winning region is not empty, it cannot also be a losing region.
    Empty regions are technically won by both players. *)
lemma nonempty_player_winning_region_exclusive:
  assumes "W \<noteq> {}"
  shows "player_winning_region W \<Longrightarrow> \<not>losing_region W"
proof -
  assume "player_winning_region W"
  with assms obtain w where "w \<in> W" "won_by_player w"
    using player_winning_region_won_by_player by fast
  hence "\<not>won_by_opponent w" using winning_v_exclusive by simp
  from \<open>w\<in>W\<close> \<open>\<not>won_by_opponent w\<close> show "\<not>losing_region W"
    using losing_region_won_by_opponent by blast
qed
end (** End of context player_paritygame. *)


section \<open>Winning Regions for Specific Players\<close>
context paritygame begin
(** Specifies winning regions for the players *)
fun winning_region where
  "winning_region EVEN = P0.player_winning_region"
| "winning_region ODD = P1.player_winning_region"

lemma winning_region_empty[simp]: "winning_region \<alpha> {}"
  by (cases \<alpha>; simp)

(** A winning region is part of the graph *)
lemma winning_region_in_V: "winning_region \<alpha> W \<Longrightarrow> W\<subseteq>V"
  using P0.player_winning_region_in_V P1.player_winning_region_in_V by (cases \<alpha>) auto

(** The player has a strategy under which their winning region is closed and all cycles reachable
    from nodes in the region are won by the player *)
lemma winning_region_strat: "winning_region \<alpha> W = (W\<subseteq>V \<and> (\<exists>\<sigma>.
  strategy_of_player \<alpha> \<sigma> \<and> dom \<sigma> = V_player \<alpha> \<inter> W \<and> ran \<sigma> \<subseteq> W \<and> E `` (W \<inter> V_opponent \<alpha>) \<subseteq> W \<and>
  (\<forall>w\<in>W. \<forall>xs. reachable_cycle (induced_subgraph \<sigma>) w xs \<longrightarrow> player_wins_list \<alpha> xs)))"
  unfolding strategy_of_player_def
  using P0.player_winning_region_def P1.player_winning_region_def V\<^sub>1_def V\<^sub>0_opposite_V\<^sub>1
  by (cases \<alpha>; simp)

(** A player can win a node *)
fun won_by where
  "won_by EVEN = P0.won_by_player"
| "won_by ODD = P1.won_by_player"

(** If a node is won by a player, it is part of the game *)
lemma won_by_in_V: "won_by \<alpha> v \<Longrightarrow> v\<in>V"
  using P0.won_by_player_in_V P1.won_by_player_in_V by (cases \<alpha>) auto

(** We can get a winning strategy for a node that is won by a player *)
lemma won_by_strat: "won_by \<alpha> v = (v \<in> V \<and> (\<exists>\<sigma>. strategy_of_player \<alpha> \<sigma> \<and>
  (\<forall>xs. reachable_cycle (induced_subgraph \<sigma>) v xs \<longrightarrow> player_wins_list \<alpha> xs)))"
  unfolding strategy_of_player_def
  by (cases \<alpha>; simp add: P0.won_by_player_def P1.won_by_player_def)

(** The winning and losing regions are symmetrical for the two sublocales *)
lemma losing_region_simps[simp]:
  "P1.losing_region = P0.player_winning_region"
  "P0.losing_region = P1.player_winning_region"
  unfolding P0.losing_region_def P1.losing_region_def
  unfolding P0.player_winning_region_def P1.player_winning_region_def
  by (auto simp: V\<^sub>1_def V_diff_diff_V\<^sub>0)

lemma won_by_opponent_simps[simp]:
  "P1.won_by_opponent = P0.won_by_player"
  "P0.won_by_opponent = P1.won_by_player"
  unfolding P0.won_by_opponent_def P1.won_by_opponent_def
  unfolding  P0.won_by_player_def P1.won_by_player_def
  by (auto simp: V\<^sub>1_def V_diff_diff_V\<^sub>0)

(** If a node is in a player's winning region, it is won by that player *)
lemma winning_region_won_by: "\<lbrakk>winning_region \<alpha> W; v\<in>W\<rbrakk> \<Longrightarrow> won_by \<alpha> v"
  using P0.player_winning_region_won_by_player P1.player_winning_region_won_by_player
  by (cases \<alpha>) auto

(** If a player's winning region is non-empty, it is not a winning region for their opponent *)
lemma nonempty_winning_region_not_winning_for_opponent:
  assumes "W \<noteq> {}"
  shows "winning_region \<alpha> W \<Longrightarrow> \<not>winning_region (opponent \<alpha>) W"
  using assms P0.nonempty_player_winning_region_exclusive P1.nonempty_player_winning_region_exclusive
  by (cases \<alpha>) auto

(** A node cannot be won by a player and their opponent at the same time. *)
lemma won_by_player_not_won_by_opponent: "\<not>(won_by \<alpha> v \<and> won_by (opponent \<alpha>) v)"
  using P0.winning_v_exclusive P1.winning_v_exclusive by (cases \<alpha>) auto
end (** End of context paritygame. *)

end
