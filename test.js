"use strict"
//logging('render') || logging('parse') || logging('rerender')

//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO make special storage vars so that unifying normal-storage makes normal->storage binding, whereas storage-storage just checks equality

import {nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, render as render, view, RK} from './mk.js'
import {logging, log, copy, toString, equals} from './util.js'

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
    let w = new SVar().name('w');
    let x = new SVar().name('x');
    let y = new SVar().name('y');
    let z = new SVar().name('z');
    let n = new SVar().name('n');


    asserte(conj(unify(x,2), reunify(x, 1)).reunify_substitution(nil.acons(x,0)).reify(x), 0); // failure
    asserte(reunify(x, 1).reunify_substitution(nil.acons(x,0)).reify(x), 1); // prim -> prim
    asserte(reunify(x, 1).reunify_substitution(nil).reify(x), 1); // free -> prim
    asserte(conj(unify(x,y), reunify(y, 1)).reunify_substitution(nil.acons(x,0)).reify(x), 1); // bound -> prim
    asserte(conde(reunify(x, 1), reunify(y, 2)).reunify_substitution(list(cons(x,0), cons(y,0))).reify([x, y]), [1, 2]); // prim -> prim x2
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

    //TODO does recursive skip work if some vars are free, so it cant check recursive order?

    /*
    asserte(x.eq(1).expand_run().asGoal(), x.eq(1)); // succeed
    asserte(x.eq(1).expand_run(list(cons(x,2))).asGoal(), x.eq(1)); // fail
    asserte(x.eq(1).conj(y.eq(2)).expand_run().asGoal(), x.eq(1).conj(y.eq(2))); // succeed & succeed
    asserte(x.eq(1).conj(y.eq(2)).expand_run(list(cons(y, 0))).asGoal(), x.eq(1).conj(y.eq(2))); // succeed & fail
    asserte(x.eq(1).conj(y.eq(2)).expand_run(list(cons(x, 0))).asGoal(), x.eq(1).conj(y.eq(2))); // fail & succeed
    asserte(x.eq(1).disj(y.eq(2)).expand_run().asGoal(), x.eq(1).disj(y.eq(2))); // succeed | succeed
    asserte(x.eq(1).disj(y.eq(2)).expand_run(list(cons(x,0), cons(y,0))).asGoal(), x.eq(1).disj(y.eq(2))); // fail | fail

    { let f = fresh(y => x.eq(1));
      asserte(f.expand_run().asGoal(), x.eq(1)); // fresh
      asserte(y.eq(2).conj(f).expand_run(list(cons(y,0))).asGoal(), y.eq(2).conj(f)); } // fail & fresh

    */
}


//asserte(fresh((x,y) => fresh((w,z,n) => [unify(x.name('x'),cons(w.name('w'), y.name('y'))), unify(w, 1), unify(y,cons(z.name('z'), n.name('n'))), unify(z,2), unify(n, nil), reunify(x, y), reunify(y, n)])).run(), List.fromTree([[[], []]])); // simultaneous delete. pointer manipulation "happens" at stratified timestep BEFORE value transfer

// x = (1 . y), y = (2)
// x->1, x->2   
// x'->y, y'->x  both x and y are at prev timestep
// x(1 . y:(2)), x->y this is deletion. y at prev timestep
// x(1 . y:(2)), y->x    (1 1 2) duplicates, but probably not super useful

// x(1 . y:(2)), y->x, x->y    this wants to set y to car and to a pair (1 . ...) CONFLICT
// x(1 . y:(2 . z:())), x->y, y->z


// DOM

{
    let model = new LVar().name('basemodel');

    // Static renders
    asserte(RK.render('lorem').root().textContent, 'lorem');
    asserte(RK.render(['span']).root().outerHTML, '<span></span>');
    asserte(RK.render(['span', 'lorem']).root().outerHTML, '<span>lorem</span>');
    asserte(RK.render(['p', ['span', 'lorem']]).root().outerHTML, '<p><span>lorem</span></p>');
    asserte(RK.render([{tagName: 'span'}, 'lorem']).root().outerHTML, '<span>lorem</span>');
    asserte(RK.render([{}, 'lorem']).root().outerHTML, '<div>lorem</div>');
    asserte(RK.render([{name: 'ipsum'}, 'lorem']).root().name, 'ipsum');
    //asserte(RK.render([{name: (v,m) => v.eq('ipsum')}, 'lorem']).root().name, 'ipsum');
    asserte(RK.render(v => v.eq('lorem')).root().textContent, 'lorem');
    asserte(RK.render(['p', v => v.eq('lorem')]).root().outerHTML, '<p>lorem</p>');
    asserte(RK.render(['p', v => fresh(x => [x.eq('lorem'), v.eq(x)])]).root().outerHTML, '<p>lorem</p>');
    asserte(RK.render(v => fresh(x => [x.eq('lorem'), v.eq(['p', x])])).root().outerHTML, '<p>lorem</p>');
    //asserte(RK.render(['p', v => 'lorem']).root().outerHTML, '<p>lorem</p>');
    //asserte(RK.render((v,m) => m, list(cons(model, 'lorem')), model).root().outerHTML, '<p>lorem</p>');
    //asserte(RK.render((v,m) => ['p', m], list(cons(model, 'lorem')), model).root().outerHTML, '<p>lorem</p>');
    asserte(render(v => fail).render().nodeType, Node.COMMENT_NODE);
    asserte(render(v => conde(v.eq('lorem'), v.eq('ipsum'))).render().textContent, 'loremipsum');
    asserte(render(['div', v => v.eq(['span', v => v.eq('lorem')])]).render().outerHTML, '<div><span>lorem</span></div>');
    asserte(render((v,m) => v.eq(m), list(cons(model,'lorem')), model).render().textContent, 'lorem');
    //asserte(render(view((v,m) => v.eq(m)).model(v => v.eq(model)), list(cons(model,'lorem'))).render().textContent, 'lorem');
    //asserte(RK.render((v,m) => v.eq(['span', m]), list(cons(model, 'lorem')), model).root().outerHTML, '<span>lorem</span>');
    asserte(render(v => fresh(x => [x.eq('lorem'), v.eq(['span', x])])).render().outerHTML, '<span>lorem</span>');
    
    // Updates before/after render
    asserte(render((v,m) => v.eq(m), list(cons(model,'lorem')), model).rerender(list(cons(model, 'ipsum')), model).render().textContent, 'ipsum'); // New template pre-render
    asserte(render((v,m) => v.eq(m), list(cons(model,'lorem')), model).prerender().rerender(list(cons(model, 'ipsum')), model).render().textContent, 'ipsum'); // New template post-render
    asserte(render((v,m) => v.eq(['span', 'ipsum']), list(cons(model,'lorem')), model).prerender().rerender(list(cons(model, 'ipsum')), model).render().outerHTML, '<span>ipsum</span>'); // New dom template post-render
    asserte(render(['p', (v,m) => v.eq(m)], list(cons(model,'lorem')), model).rerender(list(cons(model, 'ipsum')), model).render().textContent, 'ipsum'); // New subtemplate pre-render
    asserte(render(['p', (v,m) => v.eq(m)], list(cons(model,'lorem')), model).prerender().rerender(list(cons(model, 'ipsum')), model).render().outerHTML, '<p>ipsum</p>'); // New subtemplate post-render
    asserte(render(v => fresh(x => [x.eq('lorem'), v.eq(['span', x])])).prerender().rerender(nil).render().outerHTML, '<span>lorem</span>');

    // Diff single updates 
    asserte(render(['p', (v,m) => m.eq('lorem').conj(v.eq(m))], list(cons(model,'lorem')), model).render().outerHTML, '<p>lorem</p>'); // Subtemplate display
    asserte(render(['p', (v,m) => m.eq('lorem').conj(v.eq(m))], list(cons(model,'lorem')), model).prerender().rerender(list(cons(model,'ipsum'))).render().outerHTML, '<p><!----></p>'); // Subtemplate delete
    asserte(render(['p', (v,m) => m.eq('lorem').conj(v.eq(m))], list(cons(model,'ipsum')), model).prerender().rerender(list(cons(model,'lorem'))).render().outerHTML, '<p>lorem</p>'); // Subtemplate undelete
    asserte(render(['p', (v,m) => v.eq(m)], list(cons(model,'lorem')), model).prerender().rerender(list(cons(model,'ipsum'))).render().outerHTML, '<p>ipsum</p>'); // Subtemplate swap
    asserte(render(['p', (v,m) => m.eq('lorem').conj(v.eq(m))], list(cons(model,'lorem')), model).prerender().rerender(list(cons(model,'lorem'))).render().outerHTML, '<p>lorem</p>'); // Subtemplate swap identical
    asserte(render(['p', (v,m) => m.eq(list('ipsum', 'dolor')).conj(m.membero(v))], list(cons(model,list('lorem','ipsum'))), model).prerender().rerender(list(cons(model, list('ipsum', 'dolor')))).render().outerHTML, '<p>ipsumdolor</p>'); // Expand fail to branch
    asserte(render(['p', (v,m) => m.membero(v)], list(cons(model,list('lorem','ipsum'))), model).prerender().rerender(list(cons(model, list('ipsum', 'dolor')))).render().outerHTML, '<p>ipsumdolor</p>'); // Exchange cached
    /*
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => fresh((x,y) => [v.eq(x), m.eq(cons(x,y))])), list(cons(model, list('lorem', 'ipsum'))), model).render().textContent, 'lorem');    
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => fresh((x,y) => [v.eq(x), m.eq(cons(x,y))])), list(cons(model, list('lorem'))), model).prerender().rerender(list(cons(model, list('ipsum'))), model).render().textContent, 'ipsum');
    asserte(render(view((v,m) => v.eq(m)).model(v => conde(v.eq('lorem'), v.eq('ipsum')))).render().textContent, 'loremipsum');
    asserte(render(['p', view(['span', (v,m) => v.eq(m)]).model(v => conde(v.eq('lorem'), v.eq('ipsum')))]).render().outerHTML, '<p><span>lorem</span><span>ipsum</span></p>');
    asserte(render(view((v,m) => fresh(x => v.eq(m))).model((v,m) => fresh((x,y) => [m.eq('ipsum'), v.eq('dolor')])),
            list(cons(model, 'lorem')), model).prerender().rerender(list(cons(model, 'ipsum')), model).render().textContent, 'dolor');
*/

    // MODEL
    /*
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => v.eq('ipsum')), list(cons(model,'lorem')), model).render().textContent, 'ipsum'); // Static text
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => v.eq(m)), list(cons(model,'lorem')), model).prerender().rerender(list(cons(model,'ipsum')), model).render().textContent, 'ipsum'); // dynamic text
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => [m.eq('ipsum'), v.eq('ipsum')]), list(cons(model,'lorem')), model).prerender().rerender(list(cons(model,'ipsum')), model).render().textContent, 'ipsum'); //Fail -> display
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => [m.eq('lorem'), v.eq('lorem')]), list(cons(model,'lorem')), model).prerender().rerender(list(cons(model,'ipsum')), model).rerender(list(cons(model,'lorem')), model).render().textContent, 'lorem'); //Show -> hide -> show
    asserte(render(view((v,m) => v.eq(m)).model((v,m) => m.membero(v)), list(cons(model,list('lorem', 'ipsum'))), model).prerender().rerender(list(cons(model,list('ipsum', 'dolor')))).render().textContent, 'ipsumdolor');
    asserte(render(['p', view((v,m) => v.eq(m)).model((v,m) => m.membero(v))], list(cons(model,list('lorem', 'ipsum'))), model).render().outerHTML, '<p>loremipsum</p>');
    asserte(render(['p', view((v,m) => v.eq(m)).model((v,m) => m.membero(v))], list(cons(model,list('lorem', 'ipsum'))), model).prerender().rerender(list(cons(model, list('ipsum', 'dolor')))).render().outerHTML, '<p>ipsumdolor</p>');
    */
    
    // ORDER
    asserte(render((v,m,o) => conde([v.eq('ipsum'), o.eq(2)], [v.eq('lorem'), o.eq(1)])).render().textContent, 'loremipsum'); // Render order

    asserte(render(['p', (v,m,o) => m.membero(v).conj(v.eq(o))], list(cons(model,list(1,2))), model).prerender().rerender(list(cons(model, list(2,1)))).render().outerHTML, '<p>12</p>'); // Exchange cached


    // MODEL & ORDER
    //asserte(render(view((v,m) => v.eq(m)).model((v,m,o) => conde([v.eq('ipsum'), o.eq(2)], [v.eq('lorem'), o.eq(1)]))).render().textContent, 'loremipsum'); // Render order

/*
    // CACHING - VIEW
    { let v = render(['p', (v,m) => m.eq('lorem').conj(v.eq(m))], list(cons(model,'lorem')), model);
      let n = v.render().firstChild; // Failing text nodes hold renders unless overwritten
      asserte(n, v.rerender(list(cons(model,'ipsum'))).rerender(list(cons(model,'lorem'))).render().firstChild); }
    
    { let v = render(['p', (v,m) => m.eq('lorem').conj(v.eq(['span', 'lorem']))], list(cons(model,'lorem')), model);
      let n = v.render().firstChild; // Failing dom nodes hold renders
      asserte(n, v.rerender(list(cons(model,'ipsum'))).rerender(list(cons(model,'lorem'))).render().firstChild); }
    
    { let v = render(['p', (v,m) => m.membero(v)], list(cons(model,list('lorem', 'ipsum'))), model);
      let n = v.render().childNodes[1]; // View reuses eq templates in different positions
      asserte(n, v.rerender(list(cons(model,list('ipsum', 'dolor')))).render().firstChild); }

    // CACHING - MODEL
    { let v = render(['p', view((v,m) => v.eq(m)).model((v,m) => m.eq('lorem').conj(v.eq(m)))], list(cons(model,'lorem')), model);
      let n = v.render().firstChild; // Failing text nodes hold renders unless overwritten
      asserte(n, v.rerender(list(cons(model,'ipsum'))).rerender(list(cons(model,'lorem'))).render().firstChild); }

    { let v = render(['p', view((v,m) => v.eq(m)).model((v,m) => m.membero(v))], list(cons(model,list('lorem', 'ipsum'))), model);
      let n = v.render().childNodes[1]; // Model reuses eq models in different positions
      asserte(n, v.rerender(list(cons(model,list('ipsum', 'dolor')))).render().firstChild); }
*/
}


console.log('Tests Complete');
