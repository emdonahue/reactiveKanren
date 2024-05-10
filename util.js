let logging_channels = [];

function logging(on, ...channel) {
    if (!on) logging_channels = [];
    else logging_channels.push([on, ...channel]);
}

function log(...args) {
    if (logging_channels.some(ch => ch.every((e,i) => e == args[i]))) {
        console.log.apply(console, args.map(toString));
    }
    return args[args.length-1];
}

function dlog(...args) {
    console.log.apply(console, args.map(toString));
    return args[args.length-1];
}

function toString(x) {
    return !x || (x.toString && x.toString === Object.prototype.toString) ? JSON.stringify(x) : x.toString();
}


function copy(x) {
    return Object.assign(x, Object.create(Object.getPrototypeOf(x)));
}

export {logging, log, dlog, copy, toString}
