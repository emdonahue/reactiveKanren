"use strict"
//logging('render') || logging('parse') || logging('rerender')

//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize
//TODO can we quote vars to preserve references?
//TODO make special storage vars so that unifying normal-storage makes normal->storage binding, whereas storage-storage just checks equality

import {nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, render as render, view} from './mk.js'
import {logging, log, copy, toString, equals} from './util.js'

let root = document.getElementById('root');

function bench(f) {
    let measures = [];
    for (let i=0; i<10; i++) {
        performance.mark('start');
        f();
        performance.mark('end');
        measures.push(performance.measure('bench', 'start', 'end').duration);
    }
    root.replaceChildren();
    measures.sort();
    return measures[Math.floor(measures.length / 2)];
}




document.getElementById('create.appendChild').textContent = bench(() => { for (let i=0; i<10000; i++) root.appendChild(document.createElement('div'))});

document.getElementById('create.append').textContent = bench(() => {
    let children = [];
    for (let i=0; i<10000; i++) children.push(document.createElement('div'));
    root.append(...children);
});

document.getElementById('create.documentfragment').textContent = bench(() => {
    let children = document.createDocumentFragment();
    for (let i=0; i<10000; i++) children.append(document.createElement('div'));
    root.append(children);
});

document.getElementById('create.replacewith').textContent = bench(() => {
    let children = document.createElement('div');
    for (let i=0; i<10000; i++) children.append(document.createElement('div'));
    root.replaceWith(children);
});
