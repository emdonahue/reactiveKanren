"use strict"
//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO make special storage vars so that unifying normal-storage makes normal->storage binding, whereas storage-storage just checks equality

import {nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, render as render2} from './mk.js'
import {App, render, garbage_mark, garbage_sweep} from './dom.js'
import {logging, log, dlog, copy, toString, equals} from './util.js'

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



// walk all update vars first to normalize checking if a var will be updated? dont have to worry about vars shared between two terms as subterm bc physical storage is a tree
// update all children halting with any children who will get their own updates. as we walk x, check each var against current set of updates



/*
let [m, s] = normalize({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, nil);

log("model",m);
log("substitution",s);

//Model
console.assert(s.walk(m).a instanceof LVar, s.walk(m).a);
asserte(garbage_mark(s, m).length(), 10);
asserte(garbage_mark(s.acons(m.c, m.a), m).length(), 6);
asserte(garbage_sweep(s, garbage_mark(s.acons(m.c, m.a), m)).length(), 6);
*/

//Template
//asserte(render(s.walk(m).a, s, nil, m)[0].textContent, '1');

//DOM

//var o = nil; // observers: convert substitution values into dom updates


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
}


//asserte(fresh((x,y) => fresh((w,z,n) => [unify(x.name('x'),cons(w.name('w'), y.name('y'))), unify(w, 1), unify(y,cons(z.name('z'), n.name('n'))), unify(z,2), unify(n, nil), reunify(x, y), reunify(y, n)])).run(), List.fromTree([[[], []]])); // simultaneous delete. pointer manipulation "happens" at stratified timestep BEFORE value transfer

// x = (1 . y), y = (2)
// x->1, x->2   
// x'->y, y'->x  both x and y are at prev timestep
// x(1 . y:(2)), x->y this is deletion. y at prev timestep
// x(1 . y:(2)), y->x    (1 1 2) duplicates, but probably not super useful

// x(1 . y:(2)), y->x, x->y    this wants to set y to car and to a pair (1 . ...) CONFLICT
// x(1 . y:(2 . z:())), x->y, y->z




// Static templates
asserte(new App(null, 'lorem').node.textContent, 'lorem');

asserte(new App(null, ['div', 'lorem']).node.tagName, 'DIV');
asserte(new App(null, ['div', 'lorem']).node.textContent, 'lorem');

asserte(new App(null, [{tagName: 'div'}, 'lorem']).node.tagName, 'DIV');
asserte(new App(null, [{tagName: 'div'}, 'lorem']).node.textContent, 'lorem');

asserte(new App(null, [{tagName: 'div', name: 'ipsum'}, 'lorem']).node.name, 'ipsum');

asserte(new App(null, [{tagName: 'div', style: {color: 'purple'}}, 'lorem']).node.style.color, 'purple');

asserte(new App(null, ['div', ['div', 'lorem']]).node.childNodes[0].textContent, 'lorem');

//asserte(new App(null, [[null, null], 'div', 'lorem']).node.childNodes.length, 2);
//asserte(new App(null, [[null, null], 'div', 'lorem']).node.childNodes[0].textContent, 'lorem');

//asserte(new App(null, [list(null, null), 'div', 'lorem']).node.childNodes.length, 2);
//asserte(new App(null, [list(null, null), 'div', 'lorem']).node.childNodes[0].textContent, 'lorem');

// Functions
asserte(new App(null, () => 'lorem').node.textContent, 'lorem');
asserte(new App(null, [() => 'div', 'lorem']).node.tagName, 'DIV');
asserte(new App(null, [() => ({tagName: 'div'}), 'lorem']).node.tagName, 'DIV');
//asserte(new App(null, [{tagName: () => 'div'}, 'lorem']).node.tagName, 'DIV'); //TODO enable fn/goal for tagname
asserte(new App(null, [{name: () => 'ipsum'}, 'lorem']).node.name, 'ipsum');
asserte(new App(null, [{style: {color: () => 'purple'}}, 'lorem']).node.style.color, 'purple');
asserte(new App(null, ['div', () => ['div', 'lorem']]).node.childNodes[0].textContent, 'lorem');

//asserte(new App(null, [() => [null, null], 'div', 'lorem']).node.childNodes.length, 2);
//asserte(new App(null, [() => [null, null], 'div', 'lorem']).node.childNodes[0].textContent, 'lorem');

//asserte(new App(null, [() => list(null, null), 'div', 'lorem']).node.childNodes.length, 2);
//asserte(new App(null, [() => list(null, null), 'div', 'lorem']).node.childNodes[0].textContent, 'lorem');

// Goals
asserte(new App(null, x => x.eq('lorem')).node.textContent, 'lorem');
asserte(new App(null, x => fresh(y => [x.eq(y), y.eq('lorem')])).node.textContent, 'lorem');
asserte(new App(null, x => fresh(y => [x.eq(quote(y)), y.eq('lorem')])).node.textContent, 'lorem');
//asserte(new App(null, [x => x.eq('div'), 'lorem']).node.tagName, 'DIV');
//asserte(new App(null, [x => x.eq({tagName: 'div'}), 'lorem']).node.tagName, 'DIV');
asserte(new App(null, [{name: x => x.eq('ipsum')}, 'lorem']).node.name, 'ipsum');
asserte(new App(null, [{style: {color: x => x.eq('purple')}}, 'lorem']).node.style.color, 'purple');
asserte(new App(null, ['div', x => x.eq(['div', 'lorem'])]).node.outerHTML, '<div><div>lorem</div><!----></div>');

asserte(new App(null, [x => x.eq(cons(1,2)), (x,m) => m.eq({car: x})]).node.textContent, 1);

//asserte(new App(null, [x => x.eq([null, null]), 'div', 'lorem']).node.childNodes.length, 2);
//asserte(new App(null, [x => x.eq([null, null]), 'div', 'lorem']).node.childNodes[0].textContent, 'lorem');

//asserte(new App(null, [x => x.eq(list(null, null)), 'div', 'lorem']).node.childNodes.length, 2);
//asserte(new App(null, [x => x.eq(list(null, null)), 'div', 'lorem']).node.childNodes[0].textContent, 'lorem');

// Model Vars
asserte(new App('lorem', (x,m) => m).node.textContent, 'lorem');
asserte(new App('lorem', (x,m) => m).update(m => m.set('ipsum')).node.textContent, 'ipsum');
asserte(new App('lorem', (x,m) => ['div', m]).node.textContent, 'lorem');
asserte(new App('lorem', (x,m) => ['div', m]).update(m => m.set('ipsum')).node.textContent, 'ipsum');
asserte(new App('lorem', (x,m) => [{name: m}]).node.name, 'lorem');
asserte(new App('lorem', (x,m) => [{name: m}]).update(m => m.set('ipsum')).node.name, 'ipsum');
asserte(new App('red', (x,m) => [{style: {color: m}}]).node.style.color, 'red');
asserte(new App('red', (x,m) => [{style: {color: m}}]).update(m => m.set('blue')).node.style.color, 'blue');
//asserte(new App(list('lorem', 'ipsum'), (x,m) => [m, 'div', (_,e) => e]).node.textContent, 'loremipsum');
//asserte(new App(list('lorem', 'ipsum'), (x,m) => [m, 'div', (_,e) => e]).update(m => m.set(list('lorem', 'ipsum', 'dolor'))).node.textContent, 'loremipsumdolor');


asserte(new App('lorem', (x,m) => x.eq(m)).node.textContent, 'lorem');
asserte(new App('lorem', (x,m) => x.eq(m)).update(m => m.set('ipsum')).node.textContent, 'ipsum');

//asserte(new App('lorem', (x,m) => conj(x.eq('ipsum'), x.eq(m))).node.textContent, '');
asserte(new App('lorem', (x,m) => x.eq(['div', m])).node.textContent, 'lorem');
asserte(new App('lorem', (x,m) => fresh(y => [y.eq(m), x.eq(['div', y])])).node.firstChild.outerHTML, '<div>lorem<!----></div>');

asserte(new App('lorem', (x,m) => [{name: () => m}]).node.name, 'lorem');
asserte(new App('lorem', (x,m) => [{name: () => m}]).update(m => m.set('ipsum')).node.name, 'ipsum');
asserte(new App('lorem', [{name: (x,m) => conj(x.eq('ipsum'), fail)}]).node.name, undefined);



// Stratification
asserte(new App(list(1,2,3), (x,m) => m.membero(x)).node.textContent, '123');
asserte(new App(list(list(1,2), list(3,4)), [(x,m) => m.membero(x), (x,m) => m.membero(x)]).node.textContent, '1234');

//logging('run')
//logging('render', 'dynamic');

function treelist(x,m) {
    return conde([m.isNumbero(), x.eq(m)],
                 [m.isPairo(), x.eq(['div', [(y,m) => m.membero(y), treelist]])]);
}

asserte(new App(list(list(1,2), list(3,4)), treelist).node.firstChild.outerHTML, '<div><div>1<!---->2<!----><!----></div><!----><div>3<!---->4<!----><!----></div><!----><!----></div>');
//console.log(new App(list(list(1,2), list(3,4)), treelist).node.firstChild.outerHTML)

{
    let ul_template = ['ul', function ul(view, model) {
    return conde([model.isStringo(), view.eq(['li', model])],
                 [model.isPairo(), view.eq(['li', ['ul', [subview => model.membero(subview), ul]]])])}];



    asserte(new App(list(list('1','2'), list('3','4')), ul_template).node.outerHTML, '<ul><li><ul><li><ul><li>1<!----></li><!----><li>2<!----></li><!----><!----></ul></li><!----><li><ul><li>3<!----></li><!----><li>4<!----></li><!----><!----></ul></li><!----><!----></ul></li><!----></ul>');

}


// FINE GRAINED

{
    let model = new LVar();
    asserte(render2('lorem')[0].textContent, 'lorem');
    asserte(render2(['span', 'lorem'])[0].outerHTML, '<span>lorem</span>');
    asserte(render2(() => 'lorem')[0].textContent, 'lorem');
    asserte(render2(v => v.eq('lorem'))[0].textContent, 'lorem');
    asserte(render2(v => fail)[0].nodeType, Node.DOCUMENT_FRAGMENT_NODE);
    asserte(render2(v => conde(v.eq('lorem'), v.eq('ipsum')))[0].textContent, 'loremipsum');
    //console.log(render2(['div', v => conde(v.eq(['span', v => v.eq('lorem')]), v.eq(['span', v => v.eq('ipsum')]))])[0].outerHTML)
    asserte(render2(['div', v => v.eq(['span', v => v.eq('lorem')])])[0].innerHTML, '<span>lorem</span>');
    asserte(render2((v,m) => v.eq(m), list(cons(model,'lorem')), model)[0].textContent, 'lorem');


    let a = render2((v,m) => v.eq(m), list(cons(model,'lorem')), model);
    a[1].update(list(cons(model,'ipsum')));
    asserte(a[0].textContent, 'ipsum');

}



//fresh(y => [m.membero(y), x.eq(['div', []])])
//[m.isPairo(), x.eq(['div', (x,m) => [m.membero(x), treelist]])]

/*
function treelist(x,m) {
    return fresh((e,y) =>
        [m.membero(e),
         conde([e.isPairo(), treelist(y,e), x.eq(['div', y])],
               [e.isStringo(), x.eq(e)])]
    );
}

function treelist(x,m) {
    return fresh((e,y) =>
        [m.membero(e),
         conde([e.isPairo(), x.eq(['div', [e.membero(y), treelist]])],
               [e.isStringo(), x.eq(e)])]
    );
}




logging('render')
let app = new App(list(list(1, 2), 3), treelist);
console.log(app.node)
asserte(app.node.textContent, 'lorem')
*/

//asserte(new App(list(list(1, 2), 3), treelist).node.innerHTML, 'lorem');

//asserte(new App(list(list(1, 2), 3), (x,m) => [m.membero(x), treelist]).node.innerHTML, 'lorem');


// 0 or bare
// string -> text node
// list -> text node of appended
// object -> object props, no children
// goal -> ERR
// fn -> string -> textnode
// fn -> list -> textnode
// fn -> goal -> fail -> comment node
// fn -> goal -> string -> dynamic (text)
// fn -> goal -> list -> dynamic (text)
// fn -> goal -> array -> ????
// fn -> goal -> multi -> ???

// 1 child
// string -> parent tag name
// obj -> parent props
// list -> ERR
// goal -> fail -> comment
// goal -> succeed -> swap in child
// fn -> string -> parent tag name
// fn -> object -> parent props
// fn -> list -> static iterate with new models
// fn -> goal -> fail -> comment
// fn -> goal -> value -> rebuild child with new model (only need rebuild if binding variable changes)
// 




/*
// Static




asserte(render(['div', ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');

// Dynamic
var [n,,o] = render(s.walk(m).a, s, o, m);
asserte(n.textContent, '1');
//update(s.acons(s.walk(m).a, 2), o);
//asserte(n.textContent, '2');

// Lists
asserte(render([list('ipsum', 'dolor'), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([list('ipsum', 'dolor'), ['div', function (v) { return unify(v, 'lorem') }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([list('ipsum', 'dolor'), ['div', function (v, m) { return unify(v, m) }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');

// TDList
let data = {todos: [{title: 'get tds displaying', done: false},
                    {title: 'streamline api', done: true}],
            selected: quote({title: 'Untitled', done: false})};
let template = (_,m) => ['div',
                         [todos => m.unify({todos: todos}),
                          [{style: {color: (color, todo) => conde([todo.unify({done: true}), color.unify('green')],
                                                                  [todo.unify({done: false}), color.unify('black')])}},
                           [{tagName: 'input', type: 'checkbox', checked: (done, todo) => todo.unify({done: done}),
                             onchange: conde([m.unify({done: true}), reunify(m, {done: false})], //TODO make goals directly returnable?
                                             [m.unify({done: false}), reunify(m, {done: true})])}],
                           [{tagName: 'span',
                             onclick: todo => reunify(m, {selected: todo.quote()})},
                            (title, todo) => todo.eq({title: title.name('selected.title/set')})]]],
                         [{onclick: reunify(m, {selected: {title: 'SETTITLE'}})},
                          (selected, todo) => todo.eq({selected: quote({title: selected.name('selected.title/get')})})]];
*/

//let app = new App(data, template);
//document.body.appendChild(app.node);
console.log('Tests Complete');
