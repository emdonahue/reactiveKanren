"use strict"
//logging('render') || logging('parse') || logging('rerender')

//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO make special storage vars so that unifying normal-storage makes normal->storage binding, whereas storage-storage just checks equality

import {RK, list, fresh} from './mk.min.js'

let data = new Array(1000).fill(0);
data = list(...data);

function createnode() {
    let node = document.createElement('div');
    let loremipsumdolor = document.createElement('div');
    loremipsumdolor.textContent = 'loremipsumdolor';
    let sitamet = document.createElement('div');
    loremipsumdolor.textContent = 'sitamet';
    node.append(loremipsumdolor, sitamet);
    return node;
}

function bench(f) {
    let measures = [];
    for (let i=0; i<=10; i++) {
        let scratchdom = document.createElement('div');
        document.getElementById('root').appendChild(scratchdom);
        performance.mark('start');
        f(scratchdom);
        performance.mark('end');
        document.getElementById('root').replaceChildren();
        measures.push(performance.measure('bench', 'start', 'end').duration);
    }
    measures.sort();
    return measures[Math.floor(measures.length / 2)];
}

document.querySelector('#create #appendchild').textContent = bench((root) => {
    for (let i=0; i<10000; i++) root.appendChild(createnode())});

document.querySelector('#create #append').textContent = bench((root) => {
    let children = [];
    for (let i=0; i<10000; i++) children.push(createnode());
    root.append(...children);
});

document.querySelector('#create #documentfragment').textContent = bench((root) => {
    let children = document.createDocumentFragment();
    for (let i=0; i<10000; i++) children.append(createnode());
    root.append(children);
});

document.querySelector('#create #replacewith').textContent = bench((root) => {
    let children = createnode();
    for (let i=0; i<10000; i++) children.append(createnode());
    root.replaceWith(children);
});

document.querySelector('#create #clonenode').textContent = bench((root) => {
    let children = [createnode()];
    for (let i=1; i<10000; i++) children.push(children[0].cloneNode(true));
    root.append(...children);
});


document.querySelector('#create #rk').textContent = bench((root) => {
    root.append((new RK((v,m) => fresh(x => [m.membero(x), v.eq(['div', ['div', 'loremipsumdolor'], ['div', 'sitamet']])]), data)).render());
});




