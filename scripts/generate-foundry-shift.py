#!/usr/bin/env python3
"""Author the bounded Foundry shift as checked Lean declarations.

Run from the repository root, then `lake build FoundrySim.Shift`.
This authoring script assembles operation recipes, not world transitions.
All execution and all resource changes occur in the generic Lean simulator.
Each history gets distinct snapshots; observationally similar worlds never merge.
"""
from pathlib import Path
nodes=[];edges=[]
def new_node(stage,station=None,parent=None,ops=None,auto=None,label='',detail=''):
 n=len(nodes); node={'id':n,'stage':stage,'station':station,'parent':parent,'edges':[]};nodes.append(node)
 if parent is not None:
  edge={'id':len(edges),'source':parent,'target':n,'ops':ops,'auto':auto or [],'label':label,'detail':detail};edges.append(edge);nodes[parent]['edges'].append(edge)
 if stage=='root':
  for st in ['primary','secondary']:new_node('staffed',st,n,['enter'],label=f'Staff {st.title()}',detail=f'Give the {st} service line the shift’s only operator.')
 else:
  def choice(target,ops,label,detail,auto=[]):new_node(target,station,n,ops,auto,label,detail)
  if stage=='staffed':
   choice('queued',['reserve'],'Release the first lot','Reserve 10 L. Keep 10 L available for a second order.')
   choice('zero',['leave'],'Stand down','Return the operator and preserve the full 20 L supply.')
  elif stage=='queued':
   choice('active',['dispatch'],'Start production','Lock the operator and labor to the first lot.')
   choice('recovered',['dispatch','leave'],'Dispatch + depart','Both orders are valid now. Dispatch wins arbitration; departure loses. Inspect automatic failure and safe recovery.', ['fail','repair','start','leave'])
   choice('zero',['cancel'],'Cancel the order','Return the reservation and release the operator.', ['leave'])
  elif stage=='active':
   choice('buffered',['reserve'],'Build a production pipeline','Reserve the second lot while the first is active. All fuel will be committed.')
   choice('outputFirst',['advance'],'Finish the first lot','Complete one lot before deciding whether to accept another.', ['complete'])
  elif stage=='buffered':
   choice('outputBuffered',['advance'],'Finish with backlog ready','The first lot moves to output. The next lot waits for labor.', ['complete'])
  elif stage=='outputFirst':
   choice('collected',['collect'],'Deliver the first order','Collect 10 L and two service credits. Keep the operator for a possible second lot.')
   choice('outputBuffered',['reserve'],'Queue before collection','Commit the remaining fuel while the first output still occupies its bay.')
  elif stage=='collected':
   choice('ten',['leave'],'Close the shift at 10 L','Bank two credits and return the operator. Preserve 10 L for tomorrow.')
   choice('queuedSecond',['reserve'],'Take the second order','Commit the remaining 10 L for another two service credits.')
  elif stage=='queuedSecond':
   choice('activeSecond',['dispatch'],'Run the second lot','Use the returned labor for the final order.')
   choice('ten',['cancel'],'Protect the reserve','Cancel the second lot, return its fuel, and close with 10 L delivered.', ['leave'])
  elif stage=='outputBuffered':
   choice('activeSecond',['collect','dispatch'],'Clear output + dispatch','Deliver the first lot and start the second in one simultaneous order set.')
   choice('activeBlocked',['dispatch'],'Dispatch into backpressure','Start the next lot before clearing output. You must free the bay before completion.')
   choice('ten',['cancel'],'Cancel backlog and cash out','Return the second reservation and deliver the first lot.', ['collect','leave'])
  elif stage=='activeBlocked':
   choice('readyBlocked',['advance'],'Work before clearing the bay','Finish the work, leaving the output bay occupied. Completion will be blocked.')
   choice('readySecond',['collect','advance'],'Collect + advance','Clear the first lot and advance the second at the same logical tick.')
  elif stage=='readyBlocked':
   choice('readySecond',['collect'],'Clear the output bottleneck','Deliver the first lot to make room for the completed second lot.')
  elif stage=='activeSecond':
   choice('readySecond',['advance'],'Finish the second lot','Advance the final unit of work. The operator remains in active custody.')
   choice('ten',['cancelActive'],'Cancel active work safely','Return the final lot’s fuel and labor, then release the operator.', ['leave'])
  elif stage=='readySecond':
   choice('outputSecond',['complete'],'Complete the final order','Release labor and place the last output in the collection bay.')
  elif stage=='outputSecond':
   choice('twenty',['collect','leave'],'Deliver + release operator','Finish the full 20 L shift, collect four credits, and return the operator together.')
 return n
new_node('root')
titles={'root':'The night shift is yours','staffed':'Operator on station','queued':'First lot reserved','active':'Production is live','buffered':'Two lots, one labor slot','outputFirst':'The first lot is ready','collected':'Bank the shift or keep going?','queuedSecond':'One last order','outputBuffered':'The output bay is the bottleneck','activeBlocked':'Work in progress. Output occupied.','readyBlocked':'Completion is blocked','activeSecond':'The final lot is running','readySecond':'Final work complete','outputSecond':'Ready to deliver','recovered':'Outage recovered','zero':'Resources protected','ten':'A measured shift','twenty':'Full shift delivered'}
summaries={'root':'Deliver up to 20 L across two service lines. One operator, one labor unit, and one output bay per line. Balance throughput against reserves.','staffed':'Choose whether to release work. Your operator cannot staff both stations at once.','queued':'The first 10 L is reserved. Start the work or unwind the order.','active':'Labor and the operator are busy. Queue ahead for throughput, or finish one lot before committing more fuel.','buffered':'The pipeline is full: 10 L active and 10 L reserved. Complete the first order to return the shared labor.','outputFirst':'The first lot occupies output custody. Deliver it now or reserve your remaining supply.','collected':'You have delivered 10 L. Finish conservatively, or commit the remaining fuel to double production.','queuedSecond':'The second lot is funded. Dispatch it or preserve the reserve.','outputBuffered':'Both bays contain work. Collect and dispatch together, or explore what happens when output remains blocked.','activeBlocked':'The second lot is active, but the first still occupies output. Choose when to clear it.','readyBlocked':'Work is complete, but the one-slot output queue is full. Clear the first output before completing the next.','activeSecond':'The first lot has been delivered. Finish the second or cancel it safely before delivery.','readySecond':'Work is complete and output capacity is available. Complete the transformation.','outputSecond':'The second lot is in output custody. Deliver it and return the operator to close the shift.','recovered':'Dispatch won the conflict. Failure returned the active reservation; repair and restart restored service. All fuel and the operator are home.','zero':'No fuel was spent. The operator returned safely, and 20 L remains available.','ten':'10 L delivered, two credits collected, and 10 L preserved. The operator is home.','twenty':'20 L delivered. Four service credits. No stranded work. The operator and labor are safely returned.'}
L=['-- Generated by scripts/generate-foundry-shift.py; edit the phase recipes there.', 'import FoundrySim.ControlRoom','', '/-! A longer, player-directed production shift. Every branch is an ordinary', 'OperationProposal resolved by Maquina; these declarations never mutate holdings. -/', '', 'namespace Maquina.Games.Foundry.Shift','open ControlRoom Refuel Simulation','', 'private def cancelActive (station : Workcell.Station) : Workcell.Intent :=','  intent station Refuel.cancelActiveRefuel','']
def op(x,st):return f'{x} .{st}'
for node in nodes:
 n=node['id'];stage=node['stage'];st=node['station']
 if n==0:L+=['def snapshot0 : Snapshot := rootSnapshot','']
 else:
  e=next(e for e in edges if e['target']==n);p=e['source'];name=f'run{n}'
  for j,opgroup in enumerate([e['ops']]+[[x] for x in e['auto']]):
   ids=[10000+e['id']*10+j*3+i for i in range(len(opgroup))];e.setdefault('ids',ids)
   setname=f'orders{n}_{j}';runname=f'run{n}_{j}';parent=f'snapshot{p}' if j==0 else f'run{n}_{j-1}.child';snapshot_id=10000+n*10+j
   L += [f'def {setname} : OrderSet Workcell.Intent where','  orders := [ '+', '.join(f'order {cid} 10 {i} ({op(x,st)})' for i,(cid,x) in enumerate(zip(ids,opgroup)))+' ]','  idsUnique := by decide',f'def {runname} := resolveSnapshotOrderSet Workcell.executor ControlRoom.initialState',f'  {parent} ⟨{snapshot_id}⟩ rfl {setname}','']
  e['runs']=len(e['auto'])+1;L += [f'def snapshot{n} : Snapshot := run{n}_{e["runs"]-1}.child','']
 # action specs duplicate same operation per outgoing edge? candidate IDs unique globally including same op single sets different IDs okay all candidate covered no ambiguity exact order match.
 specs=[]
 for e in node['edges']:
  for i,x in enumerate(e['ops']):specs.append((10000+e['id']*10+i,x,e['label'] if len(e['ops'])==1 else x.title(),e['detail']))
 if stage=='readyBlocked':specs.append((90000+n,'complete','Complete into a full bay','Rejected: output capacity must be freed before completion.'))
 if stage=='staffed':specs.append((90000+n,'enterOther','Staff both stations','Rejected: the unique operator is already in custody.'))
 if stage in ('active','activeSecond'):specs.append((90000+n,'leave','Leave active work','Rejected: active custody keeps the operator with the running lot.'))
 # outgoing edge IDs known although child not compiled yet yes only literals.
 L += [f'def node{n} : ControlRoom.Node where',f'  snapshot := snapshot{n}',f'  title := "{titles[stage]}"',f'  summary := "{summaries[stage]}"',f'  outcome := .{("recovered" if stage=="recovered" else "conserved" if stage=="zero" else "productive") if stage in ("recovered","zero","ten","twenty") else "active"}','  candidates :=']
 if specs:
  entries=[]
  for cid,x,label,detail in specs:
   payload=f'enter .{"secondary" if st=="primary" else "primary"}' if x=='enterOther' else op(x,st)
   if st is None: payload=op(x,nodes[edges[(cid-10000)//10]['target']]['station'])
   entries.append(f'{{ candidate := candidate {cid} ({payload}), label := "{label}", detail := "{detail}" }}')
  L+=['    [ '+',\n      '.join(entries)+' ]']
 else:L+=['    []']
 L+=['  candidateIdsUnique := by decide','']
L += ['def nodes : List ControlRoom.Node := [ '+', '.join(f'node{n["id"]}' for n in nodes)+' ]','def provedNodes := nodes.map ControlRoom.provedNode','abbrev ProvedResolution := Maquina.CommandGraphResolution Workcell.executor ControlRoom.initialState provedNodes','structure Resolution where','  proof : ProvedResolution','  label : String','  summary : String','  automaticOrders : List String','']
for e in edges:
 p=e['source'];n=e['target'];eid=e['id'];runs=e['runs']
 steps=[]
 for j in range(runs):steps.append(f'provedTick '+(f'snapshot{p}' if j==0 else f'run{n}_{j-1}.child')+f' run{n}_{j}')
 exact='SameSnapshotData.refl _'
 for i in range(runs):exact=f'⟨SameSnapshotData.refl _, {exact}⟩'
 L += [f'def resolution{eid} : Resolution where','  proof :=',f'    {{ id := {eid}',f'      source := ControlRoom.provedNode node{p}',f'      target := ControlRoom.provedNode node{n}','      sourceMember := by simp [provedNodes, nodes]','      targetMember := by simp [provedNodes, nodes]',f'      actionIds := [ '+', '.join('⟨'+str(cid)+'⟩' for cid in e['ids'])+' ]','      actionIdsNonempty := by decide','      actionIdsUnique := by decide','      actionsAccepted := by native_decide','      steps := [ '+', '.join(steps)+' ]','      stepsNonempty := by decide','      firstStepActionsExact := by native_decide','      stepsConnect := by','        simp only [CommandGraphStepsConnect]',f'        exact {exact} }}',f'  label := "{e["label"]}"',f'  summary := "{e["detail"]}"','  automaticOrders := [ '+', '.join('"'+x+'"' for x in e['auto'])+' ]','']
L += ['def resolutions : List Resolution := [ '+', '.join(f'resolution{e["id"]}' for e in edges)+' ]','def provedGraph : Maquina.CommandGraph Workcell.executor ControlRoom.initialState where','  actor := operatorActor','  nodes := provedNodes','  root := ControlRoom.provedNode node0','  rootMember := by simp [provedNodes, nodes]','  nodeIdsUnique := by native_decide','  candidatesOwned := by native_decide','  resolutions := resolutions.map (·.proof)','  resolutionIdsUnique := by native_decide','  resolutionChoicesUnique := by native_decide','  acceptedCandidatesCovered := by native_decide','  terminalComplete := by native_decide','', '/-- Every scheduled rejection is a declared arbitration conflict, never a snapshot-invalid action. -/','theorem every_rejection_is_conflict :','    (resolutions.all fun resolution => resolution.proof.steps.all fun step =>','      step.events.all fun event => match event.outcome with\n        | .accepted _ => true\n        | .rejected kind _ => kind == .lostConflict) = true := by native_decide','', '/-- The complete 20 L supply is conserved at every exported decision. -/','theorem every_snapshot_conserves_fuel :','    (nodes.all fun node =>','      let world := node.snapshot.timeline.application.accounts','      decide ((world.holdings.foldl (fun total holding =>','        if holding.resourceId = fuelId then total + holding.quantity.atoms else total) 0) = 20)) = true := by native_decide','', 'end Maquina.Games.Foundry.Shift','']
Path('games/foundry/lean/FoundrySim/Shift.lean').write_text('\n'.join(L));print(len(nodes),'nodes',len(edges),'edges',len(L),'lines')
