//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize

import {nil, cons, list, Pair, List, LVar, primitive, fresh, conde, unify, setunify, normalize2, succeed, fail} from './mk.js'
import {logging, log, dlog, copy, toString} from './util.js'

function test(f, test_name) {
    try {
	f();
    } catch (x) {
	document.write('error in test: ' + (test_name || 'Unnamed'));
	throw x;
    }
}

function assert(a, ...debug_info) {
    if (!a) {
	console.log(...debug_info);
	throw Error("Assertion failed");
    }
}

function equals(a, b) {
    return JSON.stringify(a) == JSON.stringify(b);
}

function asserte(a, b) {
    if (!equals(a, b)) throw Error(toString(a) + ' != ' + toString(b));
}












// RRP
class PropObserver {
    constructor(lvar, node, attr) {
        this.lvar = lvar;
	this.node = node;
	this.attr = attr;
    }

    update(sub, obs) {
        let val = sub.walk(this.lvar);
        if (val instanceof LVar) return [sub, obs];
	this.node[this.attr] = val;
        return [sub, obs.cons(this)];
    }
}

class IterObserver {
    constructor(lvar, node, lvar_nodes, template) {
        //dlog('iter observer', lvar_nodes)
        this.lvar = lvar;
        this.node = node;
        this.lvar_nodes = lvar_nodes;
        this.template = template;
    }

    update(sub, obs, updater) {
        // get list of vars still in store
        // remove nodes for all variables no longer in store
        // for all vars in store,
        let ns = this.moddom(this.lvar, sub);
        dlog('ns', ns, this.lvar_nodes)
        dlog('sub', sub)
        this.lvar_nodes = this.lvar_nodes.filter(b => {
            if (ns.member(b.car)) return true;
            dlog('removing', b.car)
            b.cdr.remove();
            return false;
        }).append(ns.filter(v => !this.lvar_nodes.assoc(v)).map(v => {
            let node;
            [node, sub, obs] = render(this.template, sub, nil, sub.walk(v).car, () => {});
            this.node.parentNode.insertBefore(node, this.node);
            return cons(v, node);
        }));
        dlog('lvar nodes', this.lvar_nodes);
                    /*
        this.lvar_nodes = this.lvar_nodes.filter(
            function ({car:v, cdr:n}) {
                dlog('walk', v, sub.walk(v))
                if (!(sub.walk(v) instanceof Pair)) {
                    console.log('remove', sub.walk(v))
                    n.remove();
                    return false; }
                return true;
            });
*/
        //if (val instanceof Pair) return true;
        //this.node.remove();
        //return false;
        return [sub, obs.cons(this)];
    }
    moddom(lvar, sub) {
        let w = sub.walk(lvar);
        if (w === nil) {
            return nil;
        }
        assert(w instanceof Pair);
        return this.moddom(w.cdr, sub).cons(lvar);
    }
    
}



// MK


// RRP



// RENDERING

function render(spec, sub=nil, obs=nil, model={}, update=()=>{}) {
    log('render', spec, sub, obs, model);
    if (typeof spec == 'string' || typeof spec == 'number') { // Simple Text nodes
	let node = document.createTextNode(spec);
	return [node, sub, obs];
    }
    else if (spec instanceof Function) {
        return render(spec(model), sub, obs, model, update);
    }
    else if (Array.isArray(spec)) { // Build a DOM node
        let head_spec = sub.walk(spec[0]);
        if (head_spec instanceof List) { // Build an iterable DOM list
            let parent = document.createDocumentFragment();
            let items = head_spec;
            let linkvar = spec[0];
            let listvar = spec[0]; //TODO in simple static list cases this may not be a var
            let listnode = document.createComment('');
            let vars_nodes = [];
            
            while (items instanceof Pair) { //TODO deal with lvar tailed improper lists
                var [node, sub, obs] = render(spec[1], sub, obs, items.car, update);
                parent.appendChild(node);
                vars_nodes.push(cons(linkvar, node));
                linkvar = items.cdr;
                items = sub.walk(linkvar);
            }
            return [parent.appendChild(listnode) && parent, sub, obs.cons(new IterObserver(listvar, listnode, list(...vars_nodes), spec[1]))];
        } // Build a head node for the rest of the child specs
        else if (typeof head_spec == 'string'){
	    return render([{tagName:head_spec}].concat(spec.slice(1)), sub, obs, model, update);
        }
        else if (head_spec.prototype === undefined) {
            let parent = document.createElement(head_spec.tagName || 'div');
            for (let k in head_spec) {
                if (k === 'tagName') continue;
                if (k.substring(0,2) == 'on') {
                    (k => {
                        parent.addEventListener(
                            k.substring(2),
                            function(e) {
                                update(head_spec[k](model, e));
                            }
                        );})(k);
                }
                else parent[k] = head_spec[k];
            }
	    for (let i=1; i<spec.length; i++) {
	        log('child render', render(spec[i], sub, obs, model, update));
                var [node, sub, obs] = render(spec[i], sub, obs, model, update);
                parent.appendChild(node);
	    }
	    return [parent, sub, obs];
        }
        else throw Error('Unrecognized render spec head: ' + JSON.stringify(head_spec));
    }
    else if (spec instanceof LVar) { // Build a watched Text node
	var [node, sub, obs] = render(sub.walk(spec), sub, obs, model, update);
	return [node, sub, obs.cons(new PropObserver(spec, node, 'textContent'))];
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
}

// UPDATING

function update(sub, obs, updater) {
    //return obs.filter((o) => o.update(sub, obs, updater));
    return obs.fold(([sub, obs], o) => o.update(sub, obs, updater), [sub, nil])[1];
}

function garbage_collect(sub, root) { 
    return garbage_sweep(sub, garbage_mark(sub, root));
}

function garbage_mark(sub, root, marked=nil) {
    // Return vars in sub still reachable from root.
    log('garbage_mark', root, marked);
    if (root instanceof LVar) {
        if (marked.member(root)) return marked;
        return garbage_mark(sub, sub.assoc(root), marked.cons(root));
    }
    else if (primitive(root)) {
        return marked;
    }
    else {
        for (const p in root) {
            marked = garbage_mark(sub, root[p], marked);
        }
        return marked;
    }
}

function garbage_sweep(sub, marked) {
    return sub.filter((b) => marked.member(b.car));
}

// TESTING




let [m, s] = normalize2({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, nil);

log("model",m);
log("substitution",s);

//Model
assert(s.walk(m).a instanceof LVar, s.walk(m).a);
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
update(s.acons(s.walk(m).a, 2), o);
asserte(n.textContent, '2');

// Lists
asserte(render([list('ipsum', 'dolor'), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([list('ipsum', 'dolor'), ['div', function (e) { return 'lorem' }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([list('ipsum', 'dolor'), ['div', function (e) { return e }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');

// TDList
var [td_model, td_sub] =
    normalize2({todos: [{title: 'get tds displaying', done: false},
                        {title: 'streamline api', done: false}]});


function td_updater() {
    console.log(g.run(1, {reify:false, substitution: td_sub}).car.substitution + '')
    td_sub = g.run(1, {reify:false,
                       substitution: td_sub}).car.substitution;
    td_obs = update(td_sub, td_obs, td_updater);
}

var [td_node, td_sub, td_obs] =
    render(['div',
            [td_sub.walk(td_model).todos,
             [{onclick: m => {console.log('click model', m); return fresh(x => [unify({title: x}, m), setunify(x, 'event handler works')])}},
              function (e) {return td_sub.walk_path(e, 'title')}]]],
           td_sub, nil, td_model, td_updater);
asserte(td_node.childNodes.length, 3);


//console.log(td_sub.reify(td_model))
//dlog('starting model/sub',td_model, td_sub)
td_sub = fresh((x1, x2, x3) => [unify(td_model,{todos: x1}),
                                unify(x1, cons(x2, x3)),
                                setunify(x1, x3)]).run(1, {reify:false,
                                                           substitution: td_sub}).car.substitution;

//dlog('deleted model/sub', td_model, td_sub)
//dlog('garbage mark', garbage_mark(td_sub, td_model))
td_sub = garbage_collect(td_sub, td_model);
//dlog('garbage collected', td_sub)
td_obs = update(td_sub, td_obs, td_updater)
//dlog(td_sub)
console.log(td_sub.reify(td_model))

//TODO make setunify read from old and write to new
//add one
td_sub = fresh((x1, x2, x3) => [unify(td_model,{todos: cons(x2, x3)}),
                                setunify(x3, cons({title: 'add works', done: false}, nil))]).run(1, {reify:false,
                                                           substitution: td_sub}).car.substitution;

td_sub = garbage_collect(td_sub, td_model);
td_obs = update(td_sub, td_obs, td_updater)

//console.log(td_sub.reify(td_model));

/*
//setting value in place?
console.log(td_model)
console.log(fresh((td1) => [unify({todos: cons({title: td1}, new LVar())}, td_model), setunify(td1, 'updated')]).run(1, {reify: false, substitution: td_sub}).car.substitution + '' );
console.log(fresh((td1) => [unify({todos: cons({title: td1}, new LVar())}, td_model), setunify(td1, 'updated')]).run(1, {reify: false, substitution: td_sub}).car.substitution.reify(td_model));

td_sub = fresh((td1) => [unify({todos: cons({title: td1}, new LVar())}, td_model),
                         setunify(td1, 'set unify working')]).run(1, {reify: false, substitution: td_sub}).car.substitution
td_obs = update(td_sub, td_obs);

asserte(td_node.childNodes[0].innerHTML, 'set unify working');

td_sub = fresh((x1, x2) => [unify({todos: cons(new LVar(), x1)}, td_model),
                            unify(x1, cons(new LVar(), x2)),
                            setunify(x1, x2)]).run(1, {reify: false, substitution: td_sub}).car.substitution
td_sub = garbage_collect(td_sub, td_model);

td_obs = update(td_sub, td_obs);
asserte(td_node.childNodes.length, 2);
*/

document.body.appendChild(td_node);



//0: (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//tail deletion
//0: (cons #1 #2)
//1: 'test
//2: #4            (cons #3 #4)
//3 'test2
//4 nil

//head deletion
//0: #2              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//multi deletion
//0: #4              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//multi deletion
//0: #4              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//insertion
//0: (cons #1 #2)
//1: 'test
//2: (cons #6 #7)          #3
//3: (cons #4 #5)
//4 'test2
//5 nil
//6 'test3
//7 #3

//first garbage collect all unreachable items
//if a list observer is changed to something other than original object, particularly a free var, delete its node
//console.log(td_sub)



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

asserte(fresh((x) => setunify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,2), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,cons(1,2)), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x,y,z) => [unify(x,cons(y,z)), setunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2), 1, 2]]));
asserte(fresh((x) => [unify(x,1), setunify(x, cons(1,2))]).run(), List.fromTree([[cons(1, 2)]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x,{a:y}), unify(y,1), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {b:3})]).run(), List.fromTree([[{b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x,1), unify(y,2), setunify(x, y), setunify(y,x)]).run(), List.fromTree([[2, 1]]));

asserte(fresh((w,x,y,z) => {w.label = 'w'; x.label = 'x'; y.label='y'; z.label='z';
                            return [unify(x,cons(1, y)), unify(y,cons(2, nil)), unify(x,w),unify(x,cons(1, z)), setunify(w, z)]}).run(), List.fromTree([[[1], [1], [], []]])); // x,w:(1 . y,z:(2)) -> x,w:(2 . y,z:())

asserte(fresh((a,b,c,d,x,y) => {a.label='a'; b.label='b'; c.label='c'; d.label='d';
                                    x.label = 'x'; y.label='y';
                                    return [unify(a, {prop: b}), unify(b,1),
                                            unify(c, {prop: d}), unify(d,2),
                                            unify(x,cons(a, y)), unify(y,cons(c, nil)),
                                            setunify(x, y)]}).run(),
        List.fromTree([[{prop:2}, 2, {prop:2}, 2, [{prop:2}], []]]));



console.log('Tests Complete');
