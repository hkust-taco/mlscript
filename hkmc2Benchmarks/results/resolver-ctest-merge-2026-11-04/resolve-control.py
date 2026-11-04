"""Resolve the namespace-only/upstream merge used as the benchmark control.

Inputs: git merge-tree of fea7071d2 and 6a2b58bff, extracted with git archive.
Only main compiler classes from this tree enter the benchmark classpath.
"""

from pathlib import Path
import re, sys
root=Path(sys.argv[1])
pattern=re.compile(r'^<<<<<<< [^\n]+\n(.*?)^\|\|\|\|\|\|\| [^\n]+\n(.*?)^=======\n(.*?)^>>>>>>> [^\n]+\n',re.M|re.S)
def resolve(name, choose, count):
    p=root/name
    content=p.read_text()
    assert len(list(pattern.finditer(content)))==count, name
    p.write_text(pattern.sub(lambda m: choose(*m.groups()),content))
base='hkmc2/shared/src/main/scala/hkmc2/semantics/'
resolve(base+'Elaborator.scala', lambda o,b,t:t+o[o.index('    // Under new resolution'):], 1)
resolve(base+'Shape.scala', lambda o,b,t:o.replace('asyncResult','wrappedResult'), 2)
resolve(base+'NewResolver.scala', lambda o,b,t:o, 1)
p=root/(base+'NewResolver.scala')
old='''        case MemberLookup.Missing =>
          // A known miss in one wildcard source is not an error: another may provide
          // the name. Settlement diagnoses references with no candidates.
          ()'''
new='''        case MemberLookup.Missing =>
          // Eager lookup checks every alternative of a wildcard source that supplies
          // a target. Namespace lookup still follows its provider-priority rules.
          if !isNamespace(prefix) && config.language.eagerResolution && rctx.canResolve(ref) then
            rctx.missingWildcardMember(ref, prefix):
              shape.diagnostic(msg"${shape.describe.capitalize} does not contain member '${ref.id.name}'")'''
assert p.read_text().count(old)==1
p.write_text(p.read_text().replace(old,new))
for name,count in [('newres/Overrides.mls',2),('ups/syntax/PatternBody.mls',1)]:
    resolve('hkmc2/shared/src/test/mlscript/'+name,lambda o,b,t:t,count)
assert not any(re.search(r'^<<<<<<<', p.read_text(), re.M) for p in root.rglob('*.scala'))
# Preserve upstream's projected substitution in the published semantic graph,
# as well as the cache key and namespace-sensitive interpretation.
p=root/(base+'NewResolver.scala')
old='resolution.publish(TypeShape.Contextual(ContextualType(base.semantic, path :: Nil)))'
assert p.read_text().count(old)==1
p.write_text(p.read_text().replace(old,'resolution.publish(TypeShape.Contextual(ContextualType(reference.tpe.semantic, path :: Nil)))'))
print('Resolved namespace-only control with the same semantic merge decisions.')
