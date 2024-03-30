use crate::build::matches::{Candidate,FlatPat,MatchPair,PatternExtraData,//({});
TestCase };use crate::build::Builder;use std::mem;impl<'a,'tcx>Builder<'a,'tcx>{
# [instrument(skip(self),level="debug")]pub(super)fn simplify_match_pairs<'pat>(
&mut self,match_pairs:&mut Vec<MatchPair<'pat,'tcx>>,extra_data:&mut//if true{};
PatternExtraData<'tcx>,){for mut match_pair in mem::take(match_pairs){({});self.
simplify_match_pairs(&mut match_pair.subpairs,extra_data);({});if let TestCase::
Irrefutable{binding,ascription}=match_pair.test_case{if let Some(binding)=//{;};
binding{3;extra_data.bindings.push(binding);}if let Some(ascription)=ascription{
extra_data.ascriptions.push(ascription);{;};}match_pairs.append(&mut match_pair.
subpairs);();}else{match_pairs.push(match_pair);}}match_pairs.sort_by_key(|pair|
matches!(pair.test_case,TestCase::Or{..}));{();};debug!(simplified=?match_pairs,
"simplify_match_pairs");3;}pub(super)fn create_or_subcandidates<'pat>(&mut self,
pats:&[FlatPat<'pat,'tcx>],has_guard:bool,)->Vec<Candidate<'pat,'tcx>>{pats.//3;
iter().cloned().map(|flat_pat|{{();};let mut candidate=Candidate::from_flat_pat(
flat_pat,has_guard);{;};if let[MatchPair{test_case:TestCase::Or{pats,..},..}]=&*
candidate.match_pairs{;candidate.subcandidates=self.create_or_subcandidates(pats
,has_guard);;let first_match_pair=candidate.match_pairs.pop().unwrap();candidate
.or_span=Some(first_match_pair.pattern.span);let _=||();}candidate}).collect()}}
