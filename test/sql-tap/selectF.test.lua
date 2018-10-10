#!/usr/bin/env tarantool
test = require("sqltester")
test:plan(2)

--!./tcltestrunner.lua
-- 2014-03-03
--
-- The author disclaims copyright to this source code.  In place of
-- a legal notice, here is a blessing:
--
--    May you do good and not evil.
--    May you find forgiveness for yourself and forgive others.
--    May you share freely, never taking more than you give.
--
-------------------------------------------------------------------------
--
-- This file verifies that an OP_Copy operation is used instead of OP_SCopy
-- in a compound select in a case where the source register might be changed
-- before the copy is used.
--
-- ["set","testdir",[["file","dirname",["argv0"]]]]
-- ["source",[["testdir"],"\/tester.tcl"]]
testprefix = "selectF"
test:do_execsql_test(
    1,
    [[
        CREATE TABLE t1(a INT primary key, b TEXT, c TEXT);
        CREATE TABLE t2(d INT primary key, e TEXT, f TEXT);
        START TRANSACTION;
        INSERT INTO t1 VALUES(1,'one','I');
        INSERT INTO t2 VALUES(5,'ten','XX');
        INSERT INTO t2 VALUES(6,NULL,NULL);

        COMMIT;
        CREATE INDEX i1 ON t1(b, a);
    ]])

--explain_i {
--  SELECT * FROM t2
--  UNION ALL 
--  SELECT * FROM t1 WHERE a<5 
--  ORDER BY 2, 1
--}
test:do_execsql_test(
    2,
    [[
        SELECT * FROM t2
        UNION ALL 
        SELECT * FROM t1 WHERE a<5 
        ORDER BY 2, 1
    ]], {
        -- <2>
        6, "", "", 1, "one", "I", 5, "ten", "XX"
        -- </2>
    })

test:finish_test()

