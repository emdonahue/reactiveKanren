//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO can setunify(quote(var), val) let us arbitrarily unquote quotes?

import {normalize2, nil, LVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, setunify} from './mk.js'
import {App, render, garbage_mark, garbage_sweep} from './dom.js'
import {logging, log, dlog, copy, toString} from './util.js'

function test(f, test_name) {
    try {
	f();
    } catch (x) {
	document.write('error in test: ' + (test_name || 'Unnamed'));
	throw x;
    }
}

function equals(a, b) {
    return JSON.stringify(a) == JSON.stringify(b);
}

function asserte(a, b) {
    if (!equals(a, b)) throw Error(toString(a) + ' != ' + toString(b));
}






let [m, s] = normalize2({
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

//Template
asserte(render(s.walk(m).a, s, nil, m)[0].textContent, '1');

//DOM

var o = nil; // observers: convert substitution values into dom updates

// Static
asserte(render('lorem', s, o, m)[0].textContent, 'lorem');
asserte(render(['div', 'lorem'], s, o, m)[0].innerHTML, 'lorem');
asserte(render([{tagName: 'div'}], s, o, m)[0].tagName, 'DIV');
asserte(render([{tagName: 'div', name: 'lorem'}], s, o, m)[0].name, 'lorem');
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
                             onchange: conde([m.unify({done: true}), setunify(m, {done: false})], //TODO make goals directly returnable?
                                             [m.unify({done: false}), setunify(m, {done: true})])}],
                           [{tagName: 'span',
                             onclick: todo => setunify(m, {selected: todo.quote()})},
                            (title, todo) => todo.eq({title: title.name('selected.title/set')})]]],
                         [{onclick: setunify(m, {selected: {title: 'SETTITLE'}})},
                          (selected, todo) => todo.eq({selected: quote({title: selected.name('selected.title/get')})})]];


// MK TEST

asserte(succeed.run(), list(nil));
asserte(fresh((x) => unify(x, 1)).run(), List.fromTree([[1]]));
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

asserte(fresh((x) => [unify(x, 1), reunify(x, 2)]).run(), List.fromTree([[2]]));

asserte(fresh((x) => setunify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,2), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,cons(1,2)), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x,y,z) => [unify(x,cons(y,z)), setunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2), 1, 2]]));
asserte(fresh((x) => [unify(x,1), setunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2)]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x,{a:y}), unify(y,1), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {b:3})]).run(), List.fromTree([[{a:1, b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x.name('x'),1), unify(y.name('y'),2), setunify(x, y), setunify(y,x)]).run(), List.fromTree([[2, 1]]));

asserte(fresh((w,x,y,z) => [unify(x,cons(1, y)), unify(y,cons(2, nil)), unify(x,w),unify(x,cons(1, z)), setunify(w, z)]).run(), List.fromTree([[[1], [1], [], []]])); // x,w:(1 . y,z:(2)) -> x,w:(2 . y,z:())

asserte(fresh((a,b,c,d,x,y) => [unify(a, {prop: b}), unify(b,1),
                                unify(c, {prop: d}), unify(d,2),
                                unify(x,cons(a, y)), unify(y,cons(c, nil)),
                                setunify(x, y)]).run(),
        List.fromTree([[{prop:2}, 2, {prop:2}, 2, [{prop:2}], []]]));


logging('update');
//logging('unify');
//logging('init');
logging('render');
let app = new App(data, template);
document.body.appendChild(app.node);
console.log('Tests Complete');
