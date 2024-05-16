//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?

import {nil, LVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify} from './mk.js'
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

// Reunify
asserte(fresh((x) => reunify(x, 1)).run(), List.fromTree([[1]])); // free -> prim
asserte(fresh((x) => [unify(x,2), reunify(x, 1)]).run(), List.fromTree([[1]])); // prim -> prim
asserte(fresh((x) => [unify(x,cons(1,2)), reunify(x, 1)]).run(), List.fromTree([[1]])); // obj -> prim
asserte(fresh((x,y,z) => [unify(x,cons(y,z)), reunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2), 1, 2]])); // obj -> obj
asserte(fresh((x) => [unify(x,1), reunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2)]])); // prim -> obj
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), reunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1, 3]])); // normalized obj -> obj
asserte(fresh((x,y) => [unify(x,{a:y}), unify(y,1), reunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1]])); // obj -> new prop
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), reunify(x, {b:3})]).run(), List.fromTree([[{a:1, b:3}, 1, 3]])); // obj -> update prop
asserte(fresh((x,y) => [unify(x,1), unify(y,2), reunify(x, y), reunify(y,x)]).run(), List.fromTree([[2, 1]])); // swap from prev timestep
asserte(fresh((w,x,y,z) => [unify(x,cons(1, y)), unify(y,cons(2, nil)), unify(x,w),unify(x,cons(1, z)), reunify(w, z)]).run(), List.fromTree([[[1], [1], [], []]])); // x,w:(1 . y,z:(2)) -> x,w:(2 . y,z:()) delete link
asserte(fresh((a,b,c,d,x,y) => [unify(a, {prop: b}), unify(b,1),
                                unify(c, {prop: d}), unify(d,2),
                                unify(x,cons(a, y)), unify(y,cons(c, nil)),
                                reunify(x, y)]).run(),
        List.fromTree([[{prop:2}, 2, {prop:2}, 2, [{prop:2}], []]])); // delete link, update objects
asserte(fresh((x,y) => fresh((w,z,n) => [unify(x,cons(w, y)), unify(w, 1), unify(y,cons(z, n)), unify(z,1), unify(n, nil), reunify(x, y)])).run(), List.fromTree([[[1], []]])); // delete link
asserte(fresh((x,y) => fresh((w,z,n) => [unify(x.name('x'),cons(w.name('w'), y.name('y'))), unify(w, 1), unify(y,cons(z.name('z'), n.name('n'))), unify(z,2), unify(n, nil), reunify(y, x)])).run(), List.fromTree([[[1, 1, 2], [1, 2]]])); // duplicate list //x:(w:1 y:(z:2 n:nil)) -> x:(w:1 y:(z:1 n:(a:2 b:nil)))   y=x, z=w, n=(a . b), a=z, b=n. conflict fram a=z, z=w
asserte(fresh((x,y) => fresh((w,z,n) => [unify(x.name('x'),cons(w.name('w'), y.name('y'))), unify(w, 1), unify(y,cons(z.name('z'), n.name('n'))), unify(z,2), unify(n, nil), reunify(x, y), reunify(y, n)])).run(), List.fromTree([[[], []]])); // simultaneous delete. pointer manipulation "happens" at stratified timestep BEFORE value transfer

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

asserte(new App(null, ['div', [[null, null], 'lorem']]).node.childNodes.length, 3);
asserte(new App(null, ['div', [[null, null], 'lorem']]).node.childNodes[0].textContent, 'lorem');

asserte(new App(null, ['div', [list(null, null), 'lorem']]).node.childNodes.length, 3);
asserte(new App(null, ['div', [list(null, null), 'lorem']]).node.childNodes[0].textContent, 'lorem');

// Functions
asserte(new App(null, x => 'lorem').node.textContent, 'lorem');
asserte(new App(null, [x => 'div', 'lorem']).node.tagName, 'DIV');
asserte(new App(null, [x => ({tagName: 'div'}), 'lorem']).node.tagName, 'DIV');
//asserte(new App(null, [{tagName: x => 'div'}, 'lorem']).node.tagName, 'DIV'); //TODO enable fn/goal for tagname
asserte(new App(null, [{name: x => 'ipsum'}, 'lorem']).node.name, 'ipsum');
asserte(new App(null, [{style: {color: x => 'purple'}}, 'lorem']).node.style.color, 'purple');
asserte(new App(null, ['div', x => ['div', 'lorem']]).node.childNodes[0].textContent, 'lorem');

asserte(new App(null, ['div', [x => [null, null], 'lorem']]).node.childNodes.length, 3);
asserte(new App(null, ['div', [x => [null, null], 'lorem']]).node.childNodes[0].textContent, 'lorem');

asserte(new App(null, ['div', [x => list(null, null), 'lorem']]).node.childNodes.length, 3);
asserte(new App(null, ['div', [x => list(null, null), 'lorem']]).node.childNodes[0].textContent, 'lorem');

// Goals
asserte(new App(null, x => x.eq('lorem')).node.textContent, 'lorem');
asserte(new App(null, x => fresh(y => [x.eq(y), y.eq('lorem')])).node.textContent, 'lorem');
asserte(new App(null, x => fresh(y => [x.eq(quote(y)), y.eq('lorem')])).node.textContent, 'lorem');
asserte(new App(null, [x => x.eq('div'), 'lorem']).node.tagName, 'DIV');
asserte(new App(null, [x => x.eq({tagName: 'div'}), 'lorem']).node.tagName, 'DIV');
asserte(new App(null, [{name: x => x.eq('ipsum')}, 'lorem']).node.name, 'ipsum');
asserte(new App(null, [{style: {color: x => x.eq('purple')}}, 'lorem']).node.style.color, 'purple');
asserte(new App(null, ['div', x => x.eq(['div', 'lorem'])]).node.outerHTML, '<div><div>lorem</div></div>');

asserte(new App(null, ['div', [x => x.eq([null, null]), 'lorem']]).node.childNodes.length, 3);
asserte(new App(null, ['div', [x => x.eq([null, null]), 'lorem']]).node.childNodes[0].textContent, 'lorem');

asserte(new App(null, ['div', [x => x.eq(list(null, null)), 'lorem']]).node.childNodes.length, 3);
asserte(new App(null, ['div', [x => x.eq(list(null, null)), 'lorem']]).node.childNodes[0].textContent, 'lorem');

// Model

asserte(new App('lorem', (x,m) => x.eq(m)).node.textContent, 'lorem');
asserte(new App('lorem', (x,m) => x.eq(m)).update(m => m.set('ipsum')).node.textContent, 'ipsum');


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

//logging('update');
//logging('unify');
//logging('init');
//logging('render');

//let app = new App(data, template);
//document.body.appendChild(app.node);
console.log('Tests Complete');
