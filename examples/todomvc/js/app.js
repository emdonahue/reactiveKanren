import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, render as render, view} from '../../../mk.js'

(function (window) {
	'use strict';

    let template =
        ['section',
         ['header',
          ['h1', 'todos']]];
    
    let app = new RK(template);
    app.render(document.getElementById('root'));

})(window);
