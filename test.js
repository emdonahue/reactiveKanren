"use strict"
//logging('render') || logging('parse') || logging('rerender')

//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO make special storage vars so that unifying normal-storage makes normal->storage binding, whereas storage-storage just checks equality

import {nil, LVar, MVar, list, unify, quote, succeed, fresh, List, cons, conde, conj, fail, view, RK} from './mk.js'
import {logging, log, copy, toString, equals, assert} from './util.js'

function test(f, test_name) {
    try {
	f();
    } catch (x) {
	document.write('error in test: ' + (test_name || 'Unnamed'));
	throw x;
    }
}


function asserte(a, b) {
    if (!equals(a, b)) throw Error(toString(a) + ' != ' + toString(b));
}

function createDiv(child) {
    let div = document.createElement('div');
    div.append(child);
    return div;
}


// MK TEST

// Core
asserte(succeed.run(), list(nil));
asserte(fresh((x) => unify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x) => unify(x, [1,2])).run(), list(list([1,2])));
asserte(fresh((x, y) => [x.unify(1), y.unify(2)]).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => [x.unify(1), x.unify(2)]).run(), nil);
asserte(fresh((x, y) => unify(cons(x,y), cons(1,2))).run(), List.fromTree([[1, 2]]));
asserte(fresh((x, y) => unify({a:x, b:y}, {a:1, b:2})).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => unify({a:1, b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({a:1, b:2}, {b:x})).run(), List.fromTree([[2]]));
asserte(fresh((x) => conde(x.unify(1), x.unify(2))).run(2), List.fromTree([[1], [2]]));
asserte(fresh((x,y) => [unify(x,cons(1, y)), unify(y,cons(2, nil))]).run(), List.fromTree([[list(1, 2), list(2)]]));
asserte(fresh(x => [conde(unify(x,1), unify(x,1)), unify(x,1)]).run(), List.fromTree([[1], [1]]));
asserte(fresh((x) => unify(x, quote(1))).run(), List.fromTree([[1]]));
asserte(fresh((x) => unify({car:x}, cons(1,2))).run(), list());

// Lists
asserte(fresh(xs => [xs.eq(nil), xs.membero(1)]).run(), nil);
asserte(fresh(x => fresh(xs => [xs.eq(list(1)), xs.membero(x)])).run(), list(list(1)));
asserte(fresh(() => fresh(xs => [xs.eq(list(1)), xs.membero(2)])).run(), nil);
asserte(fresh(() => fresh(xs => [xs.eq(list(1)), xs.membero(1)])).run(), list(list()));
asserte(fresh(x => fresh(xs => [xs.eq(list(1, 2, 3)), xs.membero(x)])).run(), list(list(1), list(2), list(3)));

// Constraints
asserte(fresh((x) => [unify(x, 1), x.isStringo()]).run(), nil);
asserte(fresh((x) => [unify(x, 'a'), x.isStringo()]).run(), list(list('a')));
asserte(fresh((x) => [unify(x, 1), x.isNumbero()]).run(), list(list(1)));
asserte(fresh((x) => [unify(x, 'a'), x.isNumbero()]).run(), nil);
asserte(fresh((x) => [unify(x, 1), x.isPairo()]).run(), nil);
asserte(fresh((x) => [unify(x, cons(1,2)), x.isPairo()]).run(), list(list(cons(1,2))));



{ // Reunify
    let a = new LVar().name('a');
    let b = new LVar().name('b');
    let w = new MVar().name('w');
    let x = new MVar().name('x');
    let y = new MVar().name('y');
    let z = new MVar().name('z');
    let n = new MVar().name('n');

    asserte(x.set(1).rediff(nil), list(cons(x, 1)));
    asserte(x.set(1).rediff(list(cons(x, 0))), list(cons(x, 1)));
    asserte(x.set(1).rediff(list(cons(x, 1))), list());
    asserte(a.set(1).conj(a.eq(x)).rediff(nil), list(cons(x, 1)));
    asserte(x.set(a).conj(a.eq(1)).rediff(nil), list(cons(x, 1)));
    asserte(x.set(1).rediff(list(cons(x, y))), list(cons(x, 1)));
    asserte(x.set(y).rediff(list(cons(x, 0), cons(y, 0))), list(cons(x, y)));
    asserte(x.set({a:1}).rediff(list(cons(x,{a:y}), cons(y, 0))), list(cons(y, 1)));
    asserte(x.set({a:1}).rediff(list(cons(x,{a:y,b:z}), cons(y, 0), cons(z, 0))), list(cons(x, {a:y}), cons(y, 1)));
    asserte(x.set({0:1}).rediff(list(cons(x,[y]), cons(y, 0))), list(cons(x, {0:y}), cons(y, 1)));
    asserte(x.set([1]).rediff(list(cons(x,[y]), cons(y, 0))), list(cons(y, 1)));
    asserte(x.set({a:{b:1}}).rediff(list(cons(x,{a:y}), cons(y, {b:z}), cons(z, 0))), list(cons(z, 1)));
    { let d = x.set({a:1}).rediff(list(cons(x,{}))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, 1))); }
    { let d = x.set({a:1}).rediff(list(cons(x, 0))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, 1))); }
    { let d = x.set({a:y}).rediff(list(cons(x, 0))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, y))); }
    { let d = x.set({a:{b:1}}).rediff(list(cons(x,{}))), v = d.car.cdr.a, v2 = d.cdr.car.cdr.b;
      asserte(d, list(cons(x, {a: v}), cons(v, {b: v2}), cons(v2, 1))); }

    asserte(x.put(1).rediff(nil), list(cons(x, 1)));
    asserte(x.put(1).rediff(list(cons(x, 0))), list(cons(x, 1)));
    asserte(x.put(1).rediff(list(cons(x, 1))), list());
    asserte(a.put(1).conj(a.eq(x)).rediff(nil), list(cons(x, 1)));
    asserte(x.put(a).conj(a.eq(1)).rediff(nil), list(cons(x, 1)));
    asserte(x.put(1).rediff(list(cons(x, y))), list(cons(y, 1)));
    asserte(x.put(y).rediff(list(cons(x, 0), cons(y, 0))), list(cons(x, y)));
    asserte(x.put({a:1}).rediff(list(cons(x,{a:y}), cons(y, 0))), list(cons(y, 1)));
    asserte(x.put({a:1}).rediff(list(cons(x,{a:y,b:z}), cons(y, 0), cons(z, 0))), list(cons(x, {a:y}), cons(y, 1)));
    asserte(x.put({0:1}).rediff(list(cons(x,[y]), cons(y, 0))), list(cons(x, {0:y}), cons(y, 1)));
    asserte(x.put([1]).rediff(list(cons(x,[y]), cons(y, 0))), list(cons(y, 1)));
    asserte(x.put({a:{b:1}}).rediff(list(cons(x,{a:y}), cons(y, {b:z}), cons(z, 0))), list(cons(z, 1)));
    { let d = x.put({a:1}).rediff(list(cons(x,{}))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, 1))); }
    { let d = x.put({a:1}).rediff(list(cons(x, 0))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, 1))); }
    { let d = x.put({a:y}).rediff(list(cons(x, 0))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, y))); }
    { let d = x.put({a:{b:1}}).rediff(list(cons(x,{}))), v = d.car.cdr.a, v2 = d.cdr.car.cdr.b;
      asserte(d, list(cons(x, {a: v}), cons(v, {b: v2}), cons(v2, 1))); }

    asserte(x.patch(1).rediff(nil), list(cons(x, 1)));
    asserte(x.patch(1).rediff(list(cons(x, 0))), list(cons(x, 1)));
    asserte(x.patch(1).rediff(list(cons(x, 1))), list());
    asserte(a.patch(1).conj(a.eq(x)).rediff(nil), list(cons(x, 1)));
    asserte(x.patch(a).conj(a.eq(1)).rediff(nil), list(cons(x, 1)));
    asserte(x.patch(1).rediff(list(cons(x, y))), list(cons(y, 1)));
    asserte(x.put(y).rediff(list(cons(x, 0), cons(y, 0))), list(cons(x, y)));
    asserte(x.patch({a:1}).rediff(list(cons(x,{a:y}), cons(y, 0))), list(cons(y, 1)));
    asserte(x.patch({a:1}).rediff(list(cons(x,{a:y,b:z}), cons(y, 0), cons(z, 0))), list(cons(y, 1)));
    asserte(x.patch({0:1}).rediff(list(cons(x,[y]), cons(y, 0))), list(cons(x, {0:y}), cons(y, 1)));
    asserte(x.patch([1]).rediff(list(cons(x,[y]), cons(y, 0))), list(cons(y, 1)));
    asserte(x.patch({a:{b:1}}).rediff(list(cons(x,{a:y}), cons(y, {b:z}), cons(z, 0))), list(cons(z, 1)));
    { let d = x.patch({a:1}).rediff(list(cons(x,{}))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, 1))); }
    { let d = x.patch({a:1}).rediff(list(cons(x, 0))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, 1))); }
    { let d = x.patch({a:y}).rediff(list(cons(x, 0))), v = d.car.cdr.a;
      asserte(d, list(cons(x, {a: v}), cons(v, y))); }
    { let d = x.patch({a:{b:1}}).rediff(list(cons(x,{}))), v = d.car.cdr.a, v2 = d.cdr.car.cdr.b;
      asserte(d, list(cons(x, {a: v}), cons(v, {b: v2}), cons(v2, 1))); }
    
    //asserte(x.patch({a:1}).rediff(list(cons(x,0))), list(cons(y, 1)));
/*
    asserte(a.set(1).rediff(list(cons(a, x))), list(cons(x, 1)));
    asserte(x.set(y).conj(y.set(x)).rediff(list(cons(x, 1), cons(y, 2))), list(cons(y, 1), cons(x, 2)));
    */
        /*
    asserte(a.set(b).rediff(list(cons(a, x), cons(b, 1))), list(cons(x, 1)));
    asserte(a.set(y).rediff(list(cons(a, x), cons(y, 1))), list(cons(x, 1)));
    asserte(a.set(y).conj(y.set(2)).rediff(list(cons(a, x), cons(y, 1))), list(cons(y, 2), cons(x, 1)));
    asserte(a.set(y).conde(y.set(2)).rediff(list(cons(a, x), cons(y, 1))), list(cons(x, 1), cons(y, 2)));
    asserte(x.set(y).rediff(list(cons(x, cons(1, y)), cons(y, nil))), list(cons(x, nil)));
    asserte(x.set(y).conj(y.set(z)).rediff(list(cons(x, cons(1, y)), cons(y, cons(2, z)), cons(z, nil))), list(cons(x, nil)));
    asserte(x.set([z, y]).rediff(list(cons(x, [y, z]), cons(y, 1), cons(z, 2))), list(cons(x, [2, 1])));
    asserte(x.set([z, y]).conj(y.set(3)).rediff(list(cons(x, [y, z]), cons(y, 1), cons(z, 2))), list(cons(x, [2, 3])));
    asserte(x.set([y, y]).conj(y.set(3)).rediff(list(cons(x, [y, z]), cons(y, 1), cons(z, 2))), list(cons(x, [3, 3])));
    */

    asserte(nil.repatch(list(cons(x, 1))), list(cons(x, 1)));
    asserte(list(cons(x, 1)).repatch(list(cons(x, 0))), list(cons(x, 1)));
    asserte(list(cons(x, 1)).repatch(list(cons(x, y), cons(y, 0))), list(cons(x, 1), cons(y, 0)));

    asserte(list(cons(x, 1)).repatch(), list(cons(x, 1)));
    asserte(list(cons(x, 1)).repatch(list(cons(x, 0))), list(cons(x, 1)));
    asserte(list(cons(y, 1)).repatch(list(cons(x, y), cons(y, 0))), list(cons(y, 1), cons(x, y)));
    
    /*
    asserte(list(cons(x, 1)).repatch(list(cons(x, 2))), list(cons(x, 2)));
    asserte(list(cons(x, 1), cons(y,2)).repatch(list(cons(x, y))), list(cons(x, 2), cons(y,2)));
    asserte(list(cons(x, 1), cons(y,2)).repatch(list(cons(x, y), cons(y,3))), list(cons(y,3), cons(x, 3)));
    asserte(list(cons(x, cons(z,y)), cons(z, 1), cons(y,nil)).repatch(list(cons(x, list(4, 5, 6)), cons(y,list(2,3)))).reify(x), list(4,2,3));
    asserte(list(cons(x, cons(1,y)), cons(y, cons(2,z)), cons(z,nil)).repatch(list(cons(x, y), cons(y,z))).reify(x), nil);
    //asserte(list(cons(x, 1)).repatch(list(cons(x, y))), list(cons(x, 1)));
    asserte(list(cons(x, {a: y}), cons(y, 1)).repatch(list(cons(x, {a: 2}))), list(cons(x, {a: y}), cons(y, 2)));
    { let s = list(cons(x, 1)).repatch(list(cons(x, {a: 2}))), v = s.car.cdr.a;
      asserte(s, list(cons(x, {a: v}), cons(v, 2))); }
    { let s = list(cons(x, 1)).repatch(list(cons(x, {a: 2}))), v = s.car.cdr.a;
      asserte(s, list(cons(x, {a: v}), cons(v, 2))); }
    { let s = list(cons(x, 1)).repatch(list(cons(x, [2]))), v = s.car.cdr[0];
      asserte(s, list(cons(x, [v]), cons(v, 2))); }
    { let s = list(cons(x, 1)).repatch(list(cons(x, [2,3]))), v0 = s.car.cdr[0], v1 = s.car.cdr[1];
      asserte(s, list(cons(x, [v0, v1]), cons(v1, 3), cons(v0, 2))); }
    { let s = list(cons(x, 'a')).repatch(list(cons(x, ['b','c']))), v0 = s.car.cdr[0], v1 = s.car.cdr[1];
      assert(Array.isArray(s.car.cdr));
      asserte(s, list(cons(x, [v0, v1]), cons(v1, 'c'), cons(v0, 'b'))); }
    */

    
    /*
    asserte(conj(unify(x,2), reunify(x, 1)).reunify_substitution(nil.acons(x,0)).reify(x), 0); // failure
    asserte(reunify(x, 1).reunify_substitution(nil.acons(x,0)).reify(x), 1); // prim -> prim
    asserte(reunify(x, 1).reunify_substitution(nil).reify(x), 1); // free -> prim
    asserte(conj(unify(x,y), reunify(y, 1)).reunify_substitution(nil.acons(x,0)).reify(x), 1); // bound -> prim
    asserte(conde(reunify(x, 1), reunify(y, 2)).reunify_substitution(list(cons(x,0), cons(y,0))).reify([x, y]), [1, 2]); // prim -> prim x2

    asserte(reunify(x, [1]).reunify_substitution(nil).reify(x), [1]); // free -> array

    asserte(reunify(x, cons(1,2)).reunify_substitution(nil).reify(x), cons(1,2)); // free -> obj
    asserte(reunify(x, cons(1,2)).reunify_substitution(nil).length(), 3); // prim -> obj normalized
    asserte(reunify(x, 1).reunify_substitution(nil.acons(x,cons(1,2))).reify(x), 1); // obj -> prim
    asserte(reunify(x, cons(1,2)).reunify_substitution(nil.acons(x,cons(y,z))).reify(x), cons(1, 2)); // obj -> obj
    asserte(reunify(x, cons(1,2)).reunify_substitution(nil.acons(x,1)).reify(x), cons(1, 2)); // prim -> obj
    asserte(reunify(x, cons(1,2)).reunify_substitution(nil.acons(x,1)).length(), 3); // prim -> obj normalized
    asserte(reunify(x, {a:1,b:3}).reunify_substitution(list(cons(x,(x,{a:y,b:z})), cons(y,1), cons(z,2))).reify([x,y,z]), [{a:1,b:3}, 1, 3]); // normalized obj -> obj
    asserte(reunify(x, {a:1,b:3}).reunify_substitution(list(cons(x,{a:y}), cons(y,1))).reify([x,y]), [{a:1,b:3}, 1]); // obj -> new prop
    asserte(reunify(x, {b:3}).reunify_substitution(list(cons(x,{a:y,b:z}), cons(y,1), cons(z,2))).reify([x,y,z]), [{a:1, b:3}, 1, 3]); // obj -> update prop
    asserte(conj(reunify(x,y), reunify(y,x)).reunify_substitution(list(cons(x,1), cons(y,2))).reify([x,y]), [2, 1]); // swap from prev timestep
    asserte(fresh((a,b) => [reunify(a, b), unify(a,x), unify(b,y)]).reunify_substitution(list(cons(x,cons(w, y)), cons(w,1), cons(y,cons(2, nil)))).reify([x,y]), [list(2), nil]); // x,w:(1 . y,z:(2)) -> x,w:(2 . y,z:()) delete link
    asserte(fresh((b,d) => [unify(w, {prop: b}), unify(b,1),
                            unify(z, {prop: d}), unify(d,2),
                            reunify(x, y)]).reunify_substitution(list(cons(x,cons(w,y)), cons(y,cons(z,nil)))).reify([x,y]),
            [list({prop:2}), nil]); // delete link, update objects
    asserte(reunify(x, y).reunify_substitution(list(cons(x,cons(w,y)), cons(w,1), cons(y,cons(z,n)), cons(z,2), cons(n,nil))).reify(x), list(2)); // delete link
    asserte(reunify(y,x).reunify_substitution(list(cons(x,cons(w,y)), cons(w,1), cons(y,cons(z,n)), cons(z,2), cons(n,nil))).reify(x), list(1, 1, 2)); // duplicate list

    asserte(conj(reunify(x, y), reunify(y,n)).reunify_substitution(list(cons(x,cons(w,y)), cons(w,1), cons(y,cons(z,n)), cons(z,2), cons(n,nil))).reify(x), nil); // simultaneous delete link

    asserte(conj(a.unify(1), x.unify(a), a.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); // storage == bound!
    asserte(conj(a.unify(1), a.unify(x), a.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); // bound! == storage
    asserte(conj(a.unify(1), x.unify(a), x.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); // storage! == bound
    asserte(conj(a.unify(1), a.unify(x), x.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); // bound == storage!
    asserte(conj(x.unify(y), y.set(2)).reunify_substitution(list(cons(x,1), cons(y,1))).reify([x,y]), [2,2]); // storage == storage
    asserte(conj(x.unify(y), x.set(2)).reunify_substitution(list(cons(x,1), cons(y,1))).reify([x,y]), [2,2]); // storage == storage
    asserte(conj(a.unify(1), b.unify(1), b.unify(a), x.unify(a), b.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); //bound! == bound2 == storage
    asserte(conj(a.unify(1), b.unify(1), b.unify(a), x.unify(a), a.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); //bound == bound2! == storage
    asserte(conj(a.unify(1), b.unify(1), a.unify(b), x.unify(a), b.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); //bound2! == bound == storage
    asserte(conj(a.unify(1), b.unify(1), a.unify(b), x.unify(a), a.set(2)).reunify_substitution(list(cons(x,1))).reify(x), 2); //bound2 == bound! == storage
*/

}


// DOM

{
    // Static renders
    asserte(new RK('lorem').root().textContent, 'lorem');
    asserte(new RK(['span']).root().outerHTML, '<span></span>');
    asserte(new RK(['span', 'lorem']).root().outerHTML, '<span>lorem</span>');
    asserte(new RK(['p', ['span', 'lorem']]).root().outerHTML, '<p><span>lorem</span></p>');
    asserte(new RK(['p', [{tagName: 'span'}, 'lorem']]).root().outerHTML, '<p><span>lorem</span></p>');
    asserte(new RK([{tagName: 'span'}, 'lorem']).root().outerHTML, '<span>lorem</span>');
    asserte(new RK([{}, 'lorem']).root().outerHTML, '<div>lorem</div>');
    asserte(new RK([{name: 'ipsum'}, 'lorem']).root().name, 'ipsum');
    asserte(new RK([{name: v => v.eq('ipsum')}, 'lorem']).root().name, 'ipsum');
    asserte(new RK(m => [{name: v => v.eq(m)}, 'lorem'], 'ipsum').root().name, 'ipsum');
    asserte(new RK(m => v => v.eq([{name: m}, 'lorem']), 'ipsum').root().name, 'ipsum');
    asserte(new RK([{className: v => conde(v.eq('lorem'), v.eq('ipsum'))}, 'sit']).root().className, 'lorem ipsum');
    asserte(new RK(m => v => v.eq('lorem')).root().textContent, 'lorem');
    asserte(new RK(m => v => [v.eq('lorem')]).root().textContent, 'lorem');
    //asserte(new RK(v => 'lorem').root().textContent, 'lorem');
    //asserte(new RK(m => v => ['p', 'lorem']).root().outerHTML, '<p>lorem</p>');
    //asserte(new RK(m => m, 'lorem').root().textContent, 'lorem');
    //asserte(new RK(m => m, ['p', 'lorem']).root().outerHTML, '<p>lorem</p>');
    asserte(new RK(['p', v => v.eq('lorem')]).root().outerHTML, '<p>lorem</p>');
    asserte(new RK(['p', v => fresh(x => [x.eq('lorem'), v.eq(x)])]).root().outerHTML, '<p>lorem</p>');
    asserte(new RK(m => v => fresh(x => [x.eq('lorem'), v.eq(['p', x])])).root().outerHTML, '<p>lorem</p>');
    //asserte(new RK(['p', v => 'lorem']).root().outerHTML, '<p>lorem</p>');
    //asserte(new RK((v,m) => m, list(cons(model, 'lorem')), model).root().outerHTML, '<p>lorem</p>');
    //asserte(new RK((v,m) => ['p', m], list(cons(model, 'lorem')), model).root().outerHTML, '<p>lorem</p>');
    asserte(new RK(m => v => fail).root().nodeType, Node.COMMENT_NODE);
    asserte(new RK(m => v => conde(v.eq('lorem'), v.eq('ipsum'))).root().textContent, 'loremipsum');
    asserte(new RK(['div', v => v.eq(['span', v => v.eq('lorem')])]).root().outerHTML, '<div><span>lorem</span></div>');
    asserte(new RK(m => v => v.eq(m), 'lorem').root().textContent, 'lorem');
    //asserte(render(view((v,m) => v.eq(m)).model(v => v.eq(model)), list(cons(model,'lorem'))).render().textContent, 'lorem');
    //asserte(new RK((v,m) => v.eq(['span', m]), list(cons(model, 'lorem')), model).root().outerHTML, '<span>lorem</span>');
    asserte(new RK(m => v => fresh(x => [x.eq('lorem'), v.eq(['span', x])])).root().outerHTML, '<span>lorem</span>');
    //asserte(new RK(m => (v,x=m) => fresh((a,d) => [x.eq(cons(a,d)), conde(v.eq(a))]), list('lorem')).root().textContent, 'lorem');
    
    // Dynamic renders
    /*
    asserte(new RK(m => v => v.eq(m), 'lorem').root().textContent, 'lorem');
    asserte(new RK(m => v => v.eq(m), 'lorem').rerender(m => m.set('lorem')).root().textContent, 'lorem');
    asserte(new RK(m => v => v.eq(m), 'lorem').rerender(m => m.set('ipsum')).root().textContent, 'ipsum');
    asserte(new RK(m => v => v.eq(m), 'lorem').rerender(m => m.set(['p', 'ipsum'])).root().outerHTML, '<p>ipsum</p>');
    asserte(new RK(m => v => conj(m.eq('lorem'), v.eq(m)), 'lorem').rerender(m => m.set('ipsum')).root().textContent, '');

    asserte(new RK(m => v => v.eq(['p', 'lorem'])).root().outerHTML, '<p>lorem</p>');
    asserte(new RK(m => v => v.eq(['p', m]), 'lorem').root().outerHTML, '<p>lorem</p>');
    asserte(new RK(m => v => v.eq(['p', m]), 'lorem').rerender(m => m.set('ipsum')).root().outerHTML, '<p>ipsum</p>');
    asserte(new RK(m => v => v.eq(['p', v => v.eq(m)]), 'lorem').root().outerHTML, '<p>lorem</p>');
    asserte(new RK(m => v => v.eq(['p', v => v.eq(m)]), 'lorem').rerender(m => m.set('ipsum')).root().outerHTML, '<p>ipsum</p>');

    asserte(new RK(m => v => [m.eq(true), v.eq('lorem')], true).root().textContent, 'lorem');
    asserte(new RK(m => v => [m.eq(true), v.eq('lorem')], false).root().nodeType, Node.COMMENT_NODE);
    asserte(new RK(m => v => [m.eq(true), v.eq('lorem')], false).rerender(m => m.set(true)).root().textContent, 'lorem');
    asserte(new RK(m => v => [m.eq(true), v.eq('lorem')], true).rerender(m => m.set(false)).root().nodeType, Node.COMMENT_NODE);

    asserte(new RK(m => v => [m.eq(true), v.eq('lorem').conde(v.eq('ipsum'))], true).root().textContent, 'loremipsum');
    asserte(new RK(m => v => [m.eq(true), v.eq('lorem').conde(v.eq('ipsum'))], false).root().nodeType, Node.COMMENT_NODE);
    asserte(new RK(m => v => [m.eq(true), v.eq('lorem').conde(v.eq('ipsum'))], false).rerender(m => m.set(true)).root().textContent, 'loremipsum');
    asserte(new RK(m => v => [m.eq(true), v.eq('lorem').conde(v.eq('ipsum'))], true).rerender(m => m.set(false)).root().nodeType, Node.COMMENT_NODE);
    
    asserte(new RK(m => v => m.membero(v), list('lorem', 'ipsum')).root().textContent, 'loremipsum');
    asserte(new RK(m => v => m.membero(v), list('lorem', 'ipsum')).rerender(m => m.set(list('ipsum', 'dolor'))).root().textContent, 'ipsumdolor');

    asserte(new RK(m => v => m.leafo(v), cons('lorem', 'ipsum')).root().textContent, 'loremipsum');
    asserte(new RK(m => v => m.leafo(v), cons('lorem', 'dolor')).rerender(m => fresh((a,b) => [m.eq(cons(a,b)), a.set(cons('lorem', 'ipsum'))])).root().textContent, 'loremipsumdolor');

    // Dynamic In Place Updates
    { let rk = new RK(m => v => conj(m.eq('lorem'), v.eq(m)), 'lorem');
      let root = createDiv(rk.root());
      asserte(root.innerHTML, 'lorem');
      rk.rerender(m => m.set('ipsum'));
      asserte(root.innerHTML, '<!---->'); }

    { let rk = new RK(m => v => conj(m.eq('lorem'), v.eq(m)), 'ipsum');
      let root = createDiv(rk.root());
      asserte(root.innerHTML, '<!---->');
      rk.rerender(m => m.set('lorem'));
      asserte(root.innerHTML, 'lorem'); }

    { let rk = new RK(m => v => conj(m.eq('lorem'), v.eq(m)), 'lorem');
      let root = createDiv(rk.root());
      asserte(root.innerHTML, 'lorem');
      rk.rerender(m => m.set('ipsum'));
      asserte(root.innerHTML, '<!---->');
      rk.rerender(m => m.set('lorem'));
      asserte(root.innerHTML, 'lorem'); }

    { let rk = new RK(m => v => m.leafo(v), cons('lorem', 'dolor'));
      let root = createDiv(rk.root());
      asserte(root.innerHTML, 'loremdolor');
      let dolor = root.childNodes[1];
      rk.rerender(m => fresh((a,b) => [m.eq(cons(a,b)), a.set(cons('lorem', 'ipsum'))]));
      asserte(root.innerHTML, 'loremipsumdolor');
      asserte(dolor, root.childNodes[2]); }

    // Events    
    { let rk = new RK(m => [{tagName: 'p', onclick: m.set('ipsum')}, m], 'lorem');
      asserte(rk.root().outerHTML, '<p>lorem</p>');
      rk.root().click();
      asserte(rk.root().outerHTML, '<p>ipsum</p>'); }

    { let rk = new RK(m => v => fresh(x => [x.eq(m), v.eq([{tagName: 'p', onclick: x.set('ipsum')}, m])]), 'lorem');
      asserte(rk.root().outerHTML, '<p>lorem</p>');
      rk.root().click();
      asserte(rk.root().outerHTML, '<p>ipsum</p>'); }
    




    // Paper Examples

    //console.log(new RK(m => v => m.membero(v), list('lorem', 'dolor')).toString())
    //console.log(new RK(m => v => m.leafo(v), cons('lorem', 'dolor')).toString())

    asserte(fresh((x, y) => [ x.eq(y) , y.eq(1).conde(y.eq(cons(1, 2)))]).run(), list(list(1, 1), list(cons(1, 2), cons(1, 2))));
    asserte(new RK([{tagName: 'p', id: 'text'}, 'lorem ipsum']).root().outerHTML, '<p id="text">lorem ipsum</p>');
    asserte(new RK(model => [{tagName: 'p', id: 'text'}, view => view.eq(model)], 'lorem ipsum').root().outerHTML, '<p id="text">lorem ipsum</p>');
    asserte(createDiv(new RK(model => view => fresh(text => [model.membero(text), view.eq(['p', text])]), list('lorem', 'ipsum')).root()).outerHTML, '<div><p>lorem</p><p>ipsum</p></div>');

    { let rk = new RK(model => [{tagName: 'div'},
                                [{tagName: 'p'}, model],
                                [{tagName: 'button', onclick: model.set('dolor sit amet')}]], 'lorem ipsum');
      asserte(rk.root().outerHTML, '<div><p>lorem ipsum</p><button></button></div>');
      rk.root().childNodes[1].click();
      asserte(rk.root().outerHTML, '<div><p>dolor sit amet</p><button></button></div>'); }
    
    asserte(new RK(model =>
        ['ul', view => (function treeview(view, model) {
            return conde([model.isStringo(), view.eq(['li', model])],
                         [model.isPairo(),
                          view.eq(['li', ['ul',
                                          subview => fresh(submodel => [model.membero(submodel), treeview(subview, submodel)])]])])})(view, model)],
        list('lorem', list('ipsum', 'dolor'))).root().outerHTML, '<ul><li><ul><li>lorem</li><li><ul><li>ipsum</li><li>dolor</li></ul></li></ul></li></ul>');




*/

}



console.log('Tests Complete');
