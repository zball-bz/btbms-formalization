// Extracted from Codex's independent §6.1 audit harness.
import * as P from './ref-paper.mjs';

// Direct independent parsing of §6.1, without using the occurrence-map construction.
export function parseGraph(E) {
  const roles=[],edges=[],pairs=[],columns=[],entries=[];
  function walk(F,external,path) {
    const stack=external.map(x=>({...x}));
    const left=stack.length;let previous=null;
    for(let i=0;i<F.length;i++) {
      const c=left+i,id=roles.length,cp=path+'/c'+i;
      roles.push({kind:'A',column:c,path:cp});
      if(previous!==null)pairs.push([previous,id]);
      previous=id;stack.push({ordinary:id,current:id});
      const column={id,c,path:cp,entries:[]};columns.push(column);
      for(let j=0;j<F[i].length;j++) {
        const [p,H]=F[i][j],slot=roles.length,ep=cp+'/e'+j;
        if(p>=c||p<0||!stack[p])throw Error('V-invalid '+ep);
        roles.push({kind:'U',column:c,parent:p,path:ep});
        edges.push([slot,id,stack[p].ordinary]);
        if(stack[p].current!==stack[p].ordinary)edges.push([slot,id,stack[p].current]);
        const saved=stack[c].current;stack[c].current=slot;
        walk(H,stack,ep+'/h');
        stack[c].current=saved;
        const entry={slot,host:id,parent:p,height:H,end:roles.length,path:ep};
        column.entries.push(entry);entries.push(entry);
      }
    }
  }
  walk(E,[],'');
  return {roles,edges,pairs,columns,entries};
}

const numericTuple=(a,b)=>{for(let i=0;i<a.length;i++){if(a[i]!==b[i])return a[i]-b[i];}return 0;};
export function canon(G) {
  const unique=xs=>[...new Map(xs.map(x=>[x.join(','),x])).values()].sort(numericTuple);
  return {kinds:G.roles.map(x=>x.kind),edges:unique(G.edges),pairs:unique(G.pairs)};
}

// Literal §6.1 occurrence-map stages. No expression operation is used here.
export function mappedGraphs(E,maxn) {
  const s=P.stop(E);if(s.branch!=='ordinary')throw Error('not ordinary');
  const G=parseGraph(E),N=G.roles.length-1;
  const terminalEntry=G.entries.find(x=>x.slot===N),T=terminalEntry.host;
  const Rrole=G.edges.find(x=>x[0]===N)[2];
  const rootCol=G.columns.find(x=>x.id===Rrole);
  const tailCol=G.columns.find(x=>x.id===T);
  const t=s.t,r=s.r;
  let si=0,qi=0,trace=[];
  while(si<rootCol.entries.length&&qi<tailCol.entries.length-1) {
    const z=P.cmp(P.key(rootCol.entries[si].height,r),P.key(tailCol.entries[qi].height,t));
    trace.push([si,qi,z]);if(z<=0)si++;if(z>=0)qi++;
  }
  const removed=new Set();
  for(const ent of rootCol.entries.slice(0,si))for(let id=ent.slot;id<ent.end;id++)removed.add(id);
  const K=[],Q=[],D=[];
  for(let id=0;id<G.roles.length;id++) {
    if(Rrole<id&&id<T&&!removed.has(id))K.push(id);
    if(T<id&&id<N)Q.push(id);
    if(id<=Rrole||(Rrole<id&&id<T&&!removed.has(id)))D.push(id);
  }
  const Kset=new Set(K),Qset=new Set(Q),Dset=new Set(D),queryDomain=new Set([...D,T,...Q]);
  for(const edge of G.edges) {
    if(Kset.has(edge[0])&&!edge.every(x=>Dset.has(x)))throw Error('retained edge leaves D');
    if(Qset.has(edge[0])&&!edge.every(x=>queryDomain.has(x)))throw Error('query edge leaves D,T,Q');
  }
  const retainedPairs=G.pairs.filter(([,b])=>Kset.has(b));
  const queryPairs=G.pairs.filter(([,b])=>Qset.has(b)||b===T);
  for(const pair of retainedPairs)if(!pair.every(x=>Dset.has(x)))throw Error('retained pair leaves D');
  for(const pair of queryPairs)if(!pair.every(x=>queryDomain.has(x)))throw Error('query pair leaves D,T,Q');
  const H={roles:G.roles.slice(0,T),edges:G.edges.filter(x=>x.every(y=>y<T)),pairs:G.pairs.filter(x=>x.every(y=>y<T))};
  let f=new Map(D.map(x=>[x,x]));
  const results=[canon(H)];
  const roleMaps=[{latest:[...f],persistent:Array.from({length:T},(_,x)=>[x,x])}];
  function mapped(tuple,map) {return tuple.map(x=>{if(!map.has(x))throw Error('missing map '+x);return map.get(x);});}
  for(let m=0;m<maxn;m++) {
    const head=H.roles.length;H.roles.push({kind:'A'});
    const q=new Map(f);q.set(T,head);
    for(const x of Q){q.set(x,H.roles.length);H.roles.push({kind:G.roles[x].kind});}
    const next=new Map(D.filter(x=>x<Rrole).map(x=>[x,x]));next.set(Rrole,head);
    for(const x of K){next.set(x,H.roles.length);H.roles.push({kind:G.roles[x].kind});}
    for(const e of G.edges) {
      if(Qset.has(e[0]))H.edges.push(mapped(e,q));
      if(Kset.has(e[0]))H.edges.push(mapped(e,next));
    }
    for(const pair of queryPairs)H.pairs.push(mapped(pair,q));
    for(const pair of retainedPairs)H.pairs.push(mapped(pair,next));
    f=next;
    const fValues=D.map(x=>f.get(x));
    if(fValues.some((x,i)=>i>0&&x<=fValues[i-1]))throw Error('latest copy map is not order preserving');
    const qDomain=[...queryDomain].sort((a,b)=>a-b),qValues=qDomain.map(x=>q.get(x));
    if(qValues.some((x,i)=>i>0&&x<=qValues[i-1]))throw Error('query map is not order preserving');
    results.push(canon(H));roleMaps.push({latest:[...f],persistent:Array.from({length:T},(_,x)=>[x,x])});
  }
  const rootContainsStop=rootCol.entries.some(x=>x.slot<T&&T<x.end);
  const entering=G.pairs.find(([,b])=>b===T);
  return {results,roleMaps,persistentRoles:G.roles.slice(0,T),metadata:{R:Rrole,T,N,r,t,rootCursor:si,rootEntries:rootCol.entries.length,Q:Q.length,K:K.length,removed:removed.size,trace,ownerRoot:rootContainsStop,enteringPair:entering??null,largePrintedSide:K.filter(x=>G.roles[x].column>t).map(x=>({role:x,column:G.roles[x].column,path:G.roles[x].path}))}};
}

