// Independent transcription of paper §1. Tuple notation: [p,H] for entries.
export function cmp(a,b) {
  if (!Array.isArray(a)) return Math.sign(a-b);
  for(let i=0;i<Math.min(a.length,b.length);i++) {
    const c=cmp(a[i],b[i]); if(c) return c;
  }
  return Math.sign(a.length-b.length);
}
export function key(H,a) {
  return H.map(col=>col.map(([p,J])=>[p<a?[0,p]:[1,p-a],key(J,a)]));
}
export function shift(F,r,d) {
  return F.map(col=>col.map(([p,H])=>[p>=r?p+d:p,shift(H,r,d)]));
}
export function replace(F,r,d,l,Z) {
  if(l===0) return shift(F.slice(0,-1),r,d).concat(Z);
  if(!F.length||!F.at(-1).length) throw Error('route unavailable');
  return F.map((col,i)=>col.map(([p,H],j)=>[
    p>=r?p+d:p,
    i===F.length-1&&j===col.length-1?replace(H,r,d,l-1,Z):shift(H,r,d)
  ]));
}
export function seed(m) {
  if(m===0)return [[]];
  let H=[];
  for(let i=m;i>=1;i--) H=[[[i-1,H]]];
  return [[],H[0]];
}
export function stop(E) {
  if(!E.length)return {branch:'empty'};
  if(!E.at(-1).length)return {branch:'deletion'};
  let route=[E],t=E.length-1;
  for (;;) {
    const F=route.at(-1);
    if(!F.length||!F.at(-1).length) throw Error('internal empty column');
    const [r,H]=F.at(-1).at(-1);
    if(!H.length) {
      const l=route.length-1,Q=F.at(-1).slice(0,-1);
      const owner=t-F.length;
      return {branch:l>0&&!Q.length&&r===owner?'special':'ordinary',route,t,l,r,Q};
    }
    route.push(H);t+=H.length;
  }
}
export function fs(E,n) {
  const S=stop(E);
  if(S.branch==='empty')throw Error('empty has no operation');
  if(S.branch==='deletion')return E.slice(0,-1);
  const {route,t,l,r,Q}=S;
  if(S.branch==='special') {
    const F=route[l-1],P=F.at(-1).slice(0,-1),[p,H]=F.at(-1).at(-1),C=H.slice(0,-1);
    const col=P.concat(Array.from({length:n+Number(!P.length)},()=>[p,C]));
    return replace(E,0,0,l-1,[col]);
  }
  let left=0,j=0;
  while(j<route.length && r>=left+route[j].length) {left+=route[j].length;j++;}
  if(j===route.length||r<0||r>=t)throw Error('invalid parent');
  const F=route[j],i=r-left,d=t-r,R=F[i];
  let source=0,query=0;
  while(source<R.length&&query<Q.length) {
    const c=cmp(key(R[source][1],r),key(Q[query][1],t));
    if(c<=0)source++;
    if(c>=0)query++;
  }
  const U=R.slice(source);let Z=[];
  for(let k=n;k>=1;k--) {
    const newHead=shift([Q],r,(k-1)*d)[0];
    for(let a=0;a<U.length;a++) {
      const [p,H]=U[a];
      const newH=i===F.length-1&&a===U.length-1 ? replace(H,r,k*d,l-j-1,Z) : shift(H,r,k*d);
      newHead.push([p,newH]);
    }
    if(i<F.length-1)Z=[newHead,...replace(F.slice(i+1),r,k*d,l-j,Z)];
    else {if(!U.length)throw Error('empty owner-root suffix');Z=[newHead];}
  }
  return replace(E,0,0,l,Z);
}
export function word(E,e=0) {
  return E.flatMap(col=>!col.length?[[2*e,0,0]]:col.flatMap(([p,H],i)=>[
    i===0?[2*e,1,p]:[2*e+1,0,p],...word(H,e+1)
  ]));
}
export function size(E) {return E.reduce((a,col)=>a+1+col.reduce((b,[p,H])=>b+1+size(H),0),0);}
export function toRef(E) {return E.map(col=>col.map(([value,H])=>({value,height:toRef(H)})));}
export function fromRef(E) {return E.map(col=>col.map(({value,height})=>[value,fromRef(height)]));}
export function show(E) {return JSON.stringify(E);}
