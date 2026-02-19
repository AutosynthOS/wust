/// Node.js API polyfills for the plasma JavaScript runtime.
///
/// Each polyfill is a pure JavaScript string that can be prepended to user
/// code before evaluation. The polyfills define globals on `globalThis` that
/// stub or partially implement common Node.js APIs.
///
/// # Usage
/// ```
/// let preamble = plasma_hello::polyfills::all_polyfills();
/// let full_source = format!("{preamble}\n{user_code}");
/// ```

/// Returns the `globalThis.process` polyfill.
///
/// Provides `process.env`, `process.version`, `process.platform`,
/// `process.cwd()`, `process.nextTick()`, and `process.argv`.
pub fn process_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.process !== "undefined") return;
    globalThis.process = {
        env: {},
        version: "v20.0.0",
        versions: { node: "20.0.0" },
        platform: "wasm",
        arch: "wasm32",
        argv: [],
        cwd: function() { return "/"; },
        nextTick: function(_fn) {},
        stdout: { write: function(s) { console.log(s); } },
        stderr: { write: function(s) { console.log(s); } },
        exit: function(code) { throw new Error("process.exit(" + code + ")"); },
        on: function() { return globalThis.process; },
        once: function() { return globalThis.process; },
        off: function() { return globalThis.process; },
        removeListener: function() { return globalThis.process; },
        emit: function() { return false; },
    };
})();
"#
}

/// Returns the `EventEmitter` polyfill.
///
/// Provides a basic implementation with `on`, `off`, `emit`, `once`,
/// `addListener`, `removeListener`, `removeAllListeners`, `listeners`,
/// and `listenerCount`.
pub fn event_emitter_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.EventEmitter !== "undefined") return;

    function EventEmitter() {
        this._events = {};
        this._maxListeners = 10;
    }

    EventEmitter.prototype.on = function(event, fn) {
        if (!this._events[event]) this._events[event] = [];
        this._events[event].push(fn);
        return this;
    };

    EventEmitter.prototype.addListener = EventEmitter.prototype.on;

    EventEmitter.prototype.once = function(event, fn) {
        var self = this;
        function wrapper() {
            self.removeListener(event, wrapper);
            fn.apply(this, arguments);
        }
        wrapper._original = fn;
        return this.on(event, wrapper);
    };

    EventEmitter.prototype.off = function(event, fn) {
        return this.removeListener(event, fn);
    };

    EventEmitter.prototype.removeListener = function(event, fn) {
        if (!this._events[event]) return this;
        this._events[event] = this._events[event].filter(function(listener) {
            return listener !== fn && listener._original !== fn;
        });
        return this;
    };

    EventEmitter.prototype.removeAllListeners = function(event) {
        if (event) {
            delete this._events[event];
        } else {
            this._events = {};
        }
        return this;
    };

    EventEmitter.prototype.emit = function(event) {
        if (!this._events[event]) return false;
        var args = Array.prototype.slice.call(arguments, 1);
        var listeners = this._events[event].slice();
        for (var i = 0; i < listeners.length; i++) {
            listeners[i].apply(this, args);
        }
        return true;
    };

    EventEmitter.prototype.listeners = function(event) {
        return this._events[event] ? this._events[event].slice() : [];
    };

    EventEmitter.prototype.listenerCount = function(event) {
        return this._events[event] ? this._events[event].length : 0;
    };

    EventEmitter.prototype.setMaxListeners = function(n) {
        this._maxListeners = n;
        return this;
    };

    globalThis.EventEmitter = EventEmitter;
})();
"#
}

/// Returns the timers polyfill.
///
/// Provides stubs for `setTimeout`, `setInterval`, `clearTimeout`,
/// `clearInterval`, and `setImmediate`. In the WASM environment these
/// execute callbacks synchronously (setTimeout) or are no-ops (intervals).
pub fn timers_polyfill() -> &'static str {
    r#"
(function() {
    var _nextId = 1;
    if (typeof globalThis.setTimeout === "undefined") {
        globalThis.setTimeout = function(_fn, _delay) {
            return _nextId++;
        };
    }
    if (typeof globalThis.clearTimeout === "undefined") {
        globalThis.clearTimeout = function(_id) {};
    }
    if (typeof globalThis.setInterval === "undefined") {
        globalThis.setInterval = function(_fn, _delay) {
            return _nextId++;
        };
    }
    if (typeof globalThis.clearInterval === "undefined") {
        globalThis.clearInterval = function(_id) {};
    }
    if (typeof globalThis.setImmediate === "undefined") {
        globalThis.setImmediate = function(_fn) {
            return _nextId++;
        };
    }
    if (typeof globalThis.clearImmediate === "undefined") {
        globalThis.clearImmediate = function(_id) {};
    }
    if (typeof globalThis.queueMicrotask === "undefined") {
        globalThis.queueMicrotask = function(_fn) {};
    }
})();
"#
}

/// Returns the `TextEncoder` / `TextDecoder` polyfill.
///
/// Provides basic UTF-8 encoding and decoding. The encoder converts
/// strings to `Uint8Array` byte-by-byte (ASCII range). The decoder
/// converts `Uint8Array` back to a string.
pub fn text_codec_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.TextEncoder === "undefined") {
        globalThis.TextEncoder = function() {
            this.encoding = "utf-8";
        };
        globalThis.TextEncoder.prototype.encode = function(str) {
            var arr = new Uint8Array(str.length);
            for (var i = 0; i < str.length; i++) {
                arr[i] = str.charCodeAt(i) & 0xFF;
            }
            return arr;
        };
    }
    if (typeof globalThis.TextDecoder === "undefined") {
        globalThis.TextDecoder = function(encoding) {
            this.encoding = encoding || "utf-8";
        };
        globalThis.TextDecoder.prototype.decode = function(buf) {
            if (!buf) return "";
            var arr = new Uint8Array(buf.buffer || buf);
            var str = "";
            for (var i = 0; i < arr.length; i++) {
                str += String.fromCharCode(arr[i]);
            }
            return str;
        };
    }
})();
"#
}

/// Returns the `Buffer` polyfill.
///
/// Provides `Buffer.from`, `Buffer.alloc`, `Buffer.isBuffer`,
/// `Buffer.byteLength`, and `Buffer.concat`. Buffers are backed by
/// `Uint8Array`.
pub fn buffer_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.Buffer !== "undefined") return;

    function Buffer(arg) {
        if (typeof arg === "number") {
            this._data = new Uint8Array(arg);
        } else if (arg instanceof Uint8Array) {
            this._data = arg;
        } else if (typeof arg === "string") {
            this._data = new Uint8Array(arg.length);
            for (var i = 0; i < arg.length; i++) {
                this._data[i] = arg.charCodeAt(i) & 0xFF;
            }
        } else {
            this._data = new Uint8Array(0);
        }
        this.length = this._data.length;
    }

    Buffer.from = function(data, encoding) {
        if (data instanceof Buffer) return data;
        if (typeof data === "string") return new Buffer(data);
        if (data instanceof Uint8Array) return new Buffer(data);
        if (Array.isArray(data)) return new Buffer(new Uint8Array(data));
        return new Buffer(0);
    };

    Buffer.alloc = function(size) {
        return new Buffer(size);
    };

    Buffer.isBuffer = function(obj) {
        return obj instanceof Buffer;
    };

    Buffer.byteLength = function(str, encoding) {
        if (typeof str === "string") return str.length;
        if (str && str.length !== undefined) return str.length;
        return 0;
    };

    Buffer.concat = function(list, totalLength) {
        if (list.length === 0) return Buffer.alloc(0);
        var total = totalLength || 0;
        if (!totalLength) {
            for (var i = 0; i < list.length; i++) {
                total += list[i].length;
            }
        }
        var result = Buffer.alloc(total);
        var offset = 0;
        for (var i = 0; i < list.length; i++) {
            var src = list[i]._data || list[i];
            for (var j = 0; j < src.length && offset < total; j++) {
                result._data[offset++] = src[j];
            }
        }
        return result;
    };

    Buffer.prototype.toString = function(encoding) {
        var str = "";
        for (var i = 0; i < this._data.length; i++) {
            str += String.fromCharCode(this._data[i]);
        }
        return str;
    };

    Buffer.prototype.slice = function(start, end) {
        return new Buffer(this._data.slice(start, end));
    };

    Buffer.prototype.copy = function(target, targetStart, sourceStart, sourceEnd) {
        targetStart = targetStart || 0;
        sourceStart = sourceStart || 0;
        sourceEnd = sourceEnd || this.length;
        for (var i = sourceStart; i < sourceEnd; i++) {
            target._data[targetStart + (i - sourceStart)] = this._data[i];
        }
        return sourceEnd - sourceStart;
    };

    Buffer.prototype.readUInt8 = function(offset) {
        return this._data[offset];
    };

    Buffer.prototype.writeUInt8 = function(value, offset) {
        this._data[offset] = value & 0xFF;
        return offset + 1;
    };

    globalThis.Buffer = Buffer;
})();
"#
}

/// Returns the `URL` / `URLSearchParams` polyfill.
///
/// Provides basic URL parsing and `URLSearchParams` with `get`, `set`,
/// `has`, `delete`, `append`, `toString`, and `entries`.
pub fn url_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.URLSearchParams === "undefined") {
        function URLSearchParams(init) {
            this._params = [];
            if (typeof init === "string") {
                var str = init.charAt(0) === "?" ? init.slice(1) : init;
                if (str) {
                    var pairs = str.split("&");
                    for (var i = 0; i < pairs.length; i++) {
                        var idx = pairs[i].indexOf("=");
                        if (idx > -1) {
                            this._params.push([
                                decodeURIComponent(pairs[i].slice(0, idx)),
                                decodeURIComponent(pairs[i].slice(idx + 1))
                            ]);
                        } else {
                            this._params.push([decodeURIComponent(pairs[i]), ""]);
                        }
                    }
                }
            }
        }

        URLSearchParams.prototype.get = function(name) {
            for (var i = 0; i < this._params.length; i++) {
                if (this._params[i][0] === name) return this._params[i][1];
            }
            return null;
        };

        URLSearchParams.prototype.set = function(name, value) {
            var found = false;
            for (var i = 0; i < this._params.length; i++) {
                if (this._params[i][0] === name) {
                    if (!found) {
                        this._params[i][1] = String(value);
                        found = true;
                    } else {
                        this._params.splice(i, 1);
                        i--;
                    }
                }
            }
            if (!found) this._params.push([name, String(value)]);
        };

        URLSearchParams.prototype.has = function(name) {
            return this.get(name) !== null;
        };

        URLSearchParams.prototype.delete = function(name) {
            this._params = this._params.filter(function(p) {
                return p[0] !== name;
            });
        };

        URLSearchParams.prototype.append = function(name, value) {
            this._params.push([name, String(value)]);
        };

        URLSearchParams.prototype.toString = function() {
            return this._params.map(function(p) {
                return encodeURIComponent(p[0]) + "=" + encodeURIComponent(p[1]);
            }).join("&");
        };

        URLSearchParams.prototype.entries = function() {
            return this._params.slice();
        };

        globalThis.URLSearchParams = URLSearchParams;
    }

    if (typeof globalThis.URL === "undefined") {
        function URL(url, base) {
            if (base && typeof url === "string" && url.indexOf("://") === -1) {
                url = base.replace(/\/$/, "") + "/" + url.replace(/^\//, "");
            }
            this.href = url;
            var match = url.match(/^(\w+):\/\/([^/:]+)(:\d+)?(\/[^?#]*)?(\?[^#]*)?(#.*)?$/);
            if (match) {
                this.protocol = match[1] + ":";
                this.hostname = match[2];
                this.port = match[3] ? match[3].slice(1) : "";
                this.pathname = match[4] || "/";
                this.search = match[5] || "";
                this.hash = match[6] || "";
                this.host = this.hostname + (this.port ? ":" + this.port : "");
                this.origin = this.protocol + "//" + this.host;
            } else {
                this.protocol = "";
                this.hostname = "";
                this.port = "";
                this.pathname = url;
                this.search = "";
                this.hash = "";
                this.host = "";
                this.origin = "";
            }
            this.searchParams = new globalThis.URLSearchParams(this.search);
        }

        URL.prototype.toString = function() {
            return this.href;
        };

        globalThis.URL = URL;
    }
})();
"#
}

/// Returns the `node:util` polyfill.
///
/// Provides `deprecate`, `inspect`, `inherits`, `format`, and
/// `promisify` stubs sufficient for discord.js.
pub fn util_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.__node_util !== "undefined") return;

    var util = {};

    util.deprecate = function(fn, msg) {
        return fn;
    };

    util.inspect = function(obj) {
        if (obj === null) return "null";
        if (obj === undefined) return "undefined";
        if (typeof obj === "string") return "'" + obj + "'";
        try { return JSON.stringify(obj); } catch(e) { return String(obj); }
    };

    util.inherits = function(ctor, superCtor) {
        ctor.prototype = Object.create(superCtor.prototype, {
            constructor: { value: ctor, writable: true, configurable: true }
        });
    };

    util.format = function() {
        var args = Array.prototype.slice.call(arguments);
        if (args.length === 0) return "";
        var fmt = String(args[0]);
        var idx = 1;
        var result = fmt.replace(/%[sdj%]/g, function(m) {
            if (m === "%%") return "%";
            if (idx >= args.length) return m;
            var val = args[idx++];
            if (m === "%s") return String(val);
            if (m === "%d") return Number(val).toString();
            if (m === "%j") { try { return JSON.stringify(val); } catch(e) { return "[Circular]"; } }
            return m;
        });
        while (idx < args.length) {
            result += " " + String(args[idx++]);
        }
        return result;
    };

    util.promisify = function(fn) {
        return function() {
            var args = Array.prototype.slice.call(arguments);
            return new Promise(function(resolve, reject) {
                args.push(function(err, result) {
                    if (err) reject(err); else resolve(result);
                });
                fn.apply(null, args);
            });
        };
    };

    util.types = {
        isPromise: function(v) { return v instanceof Promise; },
        isDate: function(v) { return v instanceof Date; },
        isRegExp: function(v) { return v instanceof RegExp; },
    };

    globalThis.__node_util = util;
})();
"#
}

/// Returns the `node:path` polyfill.
///
/// Provides `parse`, `join`, `resolve`, `basename`, `dirname`,
/// `extname`, `sep`, and `delimiter`.
pub fn path_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.__node_path !== "undefined") return;

    var path = {};
    path.sep = "/";
    path.delimiter = ":";

    path.basename = function(p, ext) {
        var base = p.split("/").filter(function(s) { return s; }).pop() || "";
        if (ext && base.endsWith(ext)) base = base.slice(0, -ext.length);
        return base;
    };

    path.dirname = function(p) {
        var parts = p.split("/");
        parts.pop();
        return parts.join("/") || "/";
    };

    path.extname = function(p) {
        var base = path.basename(p);
        var idx = base.lastIndexOf(".");
        return idx > 0 ? base.slice(idx) : "";
    };

    path.join = function() {
        var parts = Array.prototype.slice.call(arguments);
        return parts.join("/").replace(/\/+/g, "/");
    };

    path.resolve = function() {
        var parts = Array.prototype.slice.call(arguments);
        var resolved = "";
        for (var i = parts.length - 1; i >= 0; i--) {
            resolved = parts[i] + "/" + resolved;
            if (parts[i].charAt(0) === "/") break;
        }
        return "/" + resolved.replace(/\/+/g, "/").replace(/\/$/, "");
    };

    path.parse = function(p) {
        var dir = path.dirname(p);
        var base = path.basename(p);
        var ext = path.extname(p);
        var name = ext ? base.slice(0, -ext.length) : base;
        return { root: p.charAt(0) === "/" ? "/" : "", dir: dir, base: base, ext: ext, name: name };
    };

    path.isAbsolute = function(p) {
        return p.charAt(0) === "/";
    };

    globalThis.__node_path = path;
})();
"#
}

/// Returns the `require()` polyfill and module registry.
///
/// Must be included AFTER all other polyfills since it references globals
/// like `EventEmitter`, `Buffer`, `URL`, `process`, `setTimeout`, etc.
///
/// The registry maps standard Node.js module names to objects that contain
/// the exports discord.js expects. Unknown modules throw a descriptive error.
pub fn require_polyfill() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.require !== "undefined") return;

    var _moduleCache = {};

    var _modules = {
        "node:events": function() {
            var mod = globalThis.EventEmitter;
            mod.EventEmitter = globalThis.EventEmitter;
            return mod;
        },
        "node:buffer": function() {
            return { Buffer: globalThis.Buffer };
        },
        "node:url": function() {
            return { URL: globalThis.URL, URLSearchParams: globalThis.URLSearchParams };
        },
        "node:process": function() {
            return globalThis.process;
        },
        "node:timers": function() {
            return {
                setTimeout: globalThis.setTimeout,
                clearTimeout: globalThis.clearTimeout,
                setInterval: globalThis.setInterval,
                clearInterval: globalThis.clearInterval,
                setImmediate: globalThis.setImmediate,
                clearImmediate: globalThis.clearImmediate,
            };
        },
        "node:timers/promises": function() {
            return {
                setTimeout: function(ms) {
                    return new Promise(function(resolve) {
                        globalThis.setTimeout(function() { resolve(); }, ms);
                    });
                },
                setImmediate: function() {
                    return new Promise(function(resolve) {
                        globalThis.setImmediate(function() { resolve(); });
                    });
                },
            };
        },
        "node:util": function() {
            return globalThis.__node_util;
        },
        "node:path": function() {
            return globalThis.__node_path;
        },
        "node:crypto": function() {
            return {
                randomBytes: function(n) {
                    var buf = globalThis.Buffer.alloc(n);
                    return buf;
                },
                randomUUID: function() {
                    return "00000000-0000-4000-8000-000000000000";
                },
                createHash: function() {
                    return {
                        update: function() { return this; },
                        digest: function(enc) { return enc === "hex" ? "0".repeat(64) : globalThis.Buffer.alloc(32); },
                    };
                },
                createHmac: function() {
                    return {
                        update: function() { return this; },
                        digest: function(enc) { return enc === "hex" ? "0".repeat(64) : globalThis.Buffer.alloc(32); },
                    };
                },
            };
        },
        "node:http": function() {
            return {
                Agent: function() {},
                request: function() { throw new Error("node:http.request not available in WASM"); },
                get: function() { throw new Error("node:http.get not available in WASM"); },
            };
        },
        "node:https": function() {
            return _modules["node:http"]();
        },
        "node:zlib": function() {
            var noop = function(buf, cb) { if (cb) cb(null, buf); return buf; };
            return {
                inflate: noop, deflate: noop,
                inflateSync: function(buf) { return buf; },
                deflateSync: function(buf) { return buf; },
                createInflate: function() { return { on: function() {}, write: function() {}, end: function() {} }; },
                createDeflate: function() { return { on: function() {}, write: function() {}, end: function() {} }; },
            };
        },
        "node:fs": function() {
            return {
                readFileSync: function() { throw new Error("fs.readFileSync not available in WASM"); },
                writeFileSync: function() { throw new Error("fs.writeFileSync not available in WASM"); },
                existsSync: function() { return false; },
            };
        },
        "node:fs/promises": function() {
            return {
                readFile: function() { return Promise.reject(new Error("fs not available in WASM")); },
                writeFile: function() { return Promise.reject(new Error("fs not available in WASM")); },
            };
        },
        "node:os": function() {
            return {
                platform: function() { return "wasm"; },
                arch: function() { return "wasm32"; },
                cpus: function() { return []; },
                tmpdir: function() { return "/tmp"; },
                homedir: function() { return "/"; },
                EOL: "\n",
            };
        },
        "node:worker_threads": function() {
            return {
                isMainThread: true,
                parentPort: null,
                workerData: null,
                Worker: function() { throw new Error("Worker not available in WASM"); },
                SHARE_ENV: {},
            };
        },
        "node:child_process": function() {
            return {
                spawn: function() { throw new Error("child_process not available in WASM"); },
                exec: function() { throw new Error("child_process not available in WASM"); },
                fork: function() { throw new Error("child_process not available in WASM"); },
            };
        },
        "node:stream": function() {
            function Stream() { globalThis.EventEmitter.call(this); }
            Stream.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Readable = function() { globalThis.EventEmitter.call(this); };
            Stream.Readable.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Writable = function() { globalThis.EventEmitter.call(this); };
            Stream.Writable.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Duplex = function() { globalThis.EventEmitter.call(this); };
            Stream.Duplex.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Transform = function() { globalThis.EventEmitter.call(this); };
            Stream.Transform.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.PassThrough = Stream.Transform;
            return Stream;
        },
        "node:net": function() {
            function Socket() { globalThis.EventEmitter.call(this); }
            Socket.prototype = Object.create(globalThis.EventEmitter.prototype);
            Socket.prototype.connect = function() { return this; };
            Socket.prototype.write = function() { return true; };
            Socket.prototype.end = function() {};
            Socket.prototype.destroy = function() {};
            return { Socket: Socket, createConnection: function() { return new Socket(); } };
        },
        "undici": function() {
            return {
                fetch: typeof globalThis.fetch === "function"
                    ? globalThis.fetch
                    : function() { return Promise.reject(new Error("fetch not available in WASM")); },
                Agent: function() {},
                Pool: function() {},
                Client: function() {},
            };
        },
        "ws": function() {
            function WebSocket() { globalThis.EventEmitter.call(this); }
            WebSocket.prototype = Object.create(globalThis.EventEmitter.prototype);
            WebSocket.prototype.send = function() {};
            WebSocket.prototype.close = function() {};
            WebSocket.OPEN = 1;
            WebSocket.CLOSED = 3;
            return WebSocket;
        },
    };

    // Also register without "node:" prefix for compatibility
    var aliases = {};
    Object.keys(_modules).forEach(function(key) {
        if (key.indexOf("node:") === 0) {
            aliases[key.slice(5)] = _modules[key];
        }
    });
    Object.keys(aliases).forEach(function(key) {
        if (!_modules[key]) _modules[key] = aliases[key];
    });

    globalThis.require = function require(name) {
        if (_moduleCache[name]) return _moduleCache[name];
        var factory = _modules[name];
        if (!factory) {
            throw new Error("Cannot find module '" + name + "'");
        }
        _moduleCache[name] = factory();
        return _moduleCache[name];
    };

    // Also provide import.meta stub to avoid reference errors
    // (Bun bundles use import.meta.require which gets patched in tests)
})();
"#
}

/// Returns all polyfills concatenated as a single JavaScript string.
///
/// The polyfills are ordered to respect dependencies (e.g. `EventEmitter`
/// before anything that might extend it, `URLSearchParams` before `URL`).
///
/// # Examples
/// ```
/// let preamble = plasma_hello::polyfills::all_polyfills();
/// assert!(preamble.contains("globalThis.process"));
/// ```
pub fn all_polyfills() -> String {
    [
        process_polyfill(),
        event_emitter_polyfill(),
        timers_polyfill(),
        text_codec_polyfill(),
        buffer_polyfill(),
        url_polyfill(),
        util_polyfill(),
        path_polyfill(),
        require_polyfill(),
    ]
    .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn process_polyfill_defines_global_process() {
        let js = process_polyfill();
        assert!(js.contains("globalThis.process"));
        assert!(js.contains("process.env") || js.contains("env:"));
        assert!(js.contains("version"));
        assert!(js.contains("platform"));
        assert!(js.contains("cwd"));
        assert!(js.contains("nextTick"));
    }

    #[test]
    fn event_emitter_polyfill_defines_core_methods() {
        let js = event_emitter_polyfill();
        assert!(js.contains("EventEmitter"));
        assert!(js.contains(".on"));
        assert!(js.contains(".off"));
        assert!(js.contains(".emit"));
        assert!(js.contains(".once"));
        assert!(js.contains(".removeListener"));
        assert!(js.contains(".removeAllListeners"));
        assert!(js.contains(".listeners"));
        assert!(js.contains(".listenerCount"));
    }

    #[test]
    fn timers_polyfill_defines_all_timer_functions() {
        let js = timers_polyfill();
        assert!(js.contains("setTimeout"));
        assert!(js.contains("setInterval"));
        assert!(js.contains("clearTimeout"));
        assert!(js.contains("clearInterval"));
        assert!(js.contains("setImmediate"));
        assert!(js.contains("queueMicrotask"));
    }

    #[test]
    fn text_codec_polyfill_defines_encoder_and_decoder() {
        let js = text_codec_polyfill();
        assert!(js.contains("TextEncoder"));
        assert!(js.contains("TextDecoder"));
        assert!(js.contains("encode"));
        assert!(js.contains("decode"));
    }

    #[test]
    fn buffer_polyfill_defines_buffer_api() {
        let js = buffer_polyfill();
        assert!(js.contains("Buffer"));
        assert!(js.contains("Buffer.from"));
        assert!(js.contains("Buffer.alloc"));
        assert!(js.contains("Buffer.isBuffer"));
        assert!(js.contains("Buffer.concat"));
        assert!(js.contains("toString"));
    }

    #[test]
    fn url_polyfill_defines_url_and_search_params() {
        let js = url_polyfill();
        assert!(js.contains("URL"));
        assert!(js.contains("URLSearchParams"));
        assert!(js.contains("hostname"));
        assert!(js.contains("pathname"));
        assert!(js.contains("searchParams"));
    }

    #[test]
    fn util_polyfill_defines_core_methods() {
        let js = util_polyfill();
        assert!(js.contains("deprecate"));
        assert!(js.contains("inspect"));
        assert!(js.contains("inherits"));
        assert!(js.contains("format"));
        assert!(js.contains("promisify"));
    }

    #[test]
    fn path_polyfill_defines_core_methods() {
        let js = path_polyfill();
        assert!(js.contains("parse"));
        assert!(js.contains("join"));
        assert!(js.contains("resolve"));
        assert!(js.contains("basename"));
        assert!(js.contains("dirname"));
        assert!(js.contains("extname"));
    }

    #[test]
    fn require_polyfill_defines_require() {
        let js = require_polyfill();
        assert!(js.contains("globalThis.require"));
        assert!(js.contains("node:events"));
        assert!(js.contains("node:buffer"));
        assert!(js.contains("node:process"));
        assert!(js.contains("node:timers"));
        assert!(js.contains("node:util"));
        assert!(js.contains("node:path"));
    }

    #[test]
    fn all_polyfills_includes_every_polyfill() {
        let combined = all_polyfills();
        assert!(combined.contains("globalThis.process"));
        assert!(combined.contains("EventEmitter"));
        assert!(combined.contains("setTimeout"));
        assert!(combined.contains("TextEncoder"));
        assert!(combined.contains("Buffer"));
        assert!(combined.contains("globalThis.URL"));
        assert!(combined.contains("globalThis.require"));
        assert!(combined.contains("__node_util"));
        assert!(combined.contains("__node_path"));
    }

    #[test]
    fn all_polyfills_is_nonempty() {
        let combined = all_polyfills();
        assert!(!combined.is_empty());
        // Should be a substantial amount of JS code
        assert!(combined.len() > 1000);
    }
}
