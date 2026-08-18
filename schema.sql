-- this is a copy of schema.sql as it existed as of `caf25e2` aka `foamcore~1`. the Lean references
-- apply to *that* tree, probably not to HEAD as of whatever ref you're reading right now. :) it's
-- here as a sort a hmmm a tuning fork, maybe

CREATE SCHEMA IF NOT EXISTS foam;

CREATE EXTENSION IF NOT EXISTS pgcrypto;

CREATE OR REPLACE FUNCTION foam.caddr(c int[]) RETURNS uuid LANGUAGE sql IMMUTABLE AS
  $$ SELECT encode(substring(digest(coalesce(array_to_string(c,':'),''),'sha256') FROM 1 FOR 16),'hex')::uuid $$;

CREATE TABLE IF NOT EXISTS foam.observer (
  id     uuid PRIMARY KEY,
  parent uuid REFERENCES foam.observer (id)
);
INSERT INTO foam.observer (id, parent)
  VALUES ('00000000-0000-0000-0000-000000000000', NULL) ON CONFLICT DO NOTHING;

-- Foam/Seat/Beholder.lean
-- Foam/Seat/Meet.lean
INSERT INTO foam.observer (id, parent)
  VALUES ('00000000-0000-0000-0000-000000000001',
          '00000000-0000-0000-0000-000000000000') ON CONFLICT DO NOTHING;

CREATE OR REPLACE FUNCTION foam.root() RETURNS uuid LANGUAGE sql IMMUTABLE AS
  $$ SELECT '00000000-0000-0000-0000-000000000000'::uuid $$;

CREATE OR REPLACE FUNCTION foam.bench() RETURNS uuid LANGUAGE sql IMMUTABLE AS
  $$ SELECT '00000000-0000-0000-0000-000000000001'::uuid $$;

-- Foam/Seat/Meet.lean
CREATE OR REPLACE FUNCTION foam.ancestry(o uuid) RETURNS uuid[] LANGUAGE sql STABLE AS $$
  WITH RECURSIVE chain(id, parent) AS (
    SELECT o, (SELECT parent FROM foam.observer WHERE id = o)
    UNION
    SELECT ob.id, ob.parent FROM chain JOIN foam.observer ob ON ob.id = chain.parent
  )
  SELECT array_agg(id) FROM chain
$$;

-- Foam/Scar.lean
CREATE OR REPLACE FUNCTION foam.lineage(o uuid) RETURNS uuid[] LANGUAGE sql STABLE AS $$
  WITH RECURSIVE chain(id, parent, depth, seen) AS (
    SELECT o, (SELECT parent FROM foam.observer WHERE id = o), 0, ARRAY[o]
    UNION ALL
    SELECT ob.id, ob.parent, chain.depth + 1, chain.seen || ob.id
    FROM chain JOIN foam.observer ob ON ob.id = chain.parent
    WHERE NOT ob.id = ANY(chain.seen)
  )
  SELECT array_agg(id ORDER BY depth DESC) FROM chain
$$;

-- Foam/Seat/Meet.lean
CREATE OR REPLACE FUNCTION foam.meet(a uuid, b uuid) RETURNS uuid LANGUAGE sql STABLE AS $$
  WITH la AS (SELECT id, ord FROM unnest(foam.lineage(a)) WITH ORDINALITY AS t(id, ord)),
       lb AS (SELECT id FROM unnest(foam.lineage(b)) AS t(id))
  SELECT la.id FROM la JOIN lb USING (id) ORDER BY la.ord DESC LIMIT 1
$$;

-- Foam/Seat/Meet.lean
CREATE OR REPLACE FUNCTION foam.grade(a uuid, b uuid) RETURNS int LANGUAGE sql STABLE AS $$
  SELECT count(*)::int FROM (
    SELECT id FROM unnest(foam.lineage(a)) AS t(id)
    INTERSECT
    SELECT id FROM unnest(foam.lineage(b)) AS t(id)
  ) shared
$$;

-- Foam/Seat/Meet.lean
-- Foam/Seat/Descend.lean
-- Foam/Seat/Rendezvous.lean
CREATE OR REPLACE FUNCTION foam.descend(parent uuid DEFAULT foam.root()) RETURNS uuid
  LANGUAGE sql AS
  $$ INSERT INTO foam.observer (id, parent) VALUES (gen_random_uuid(), parent)
     RETURNING id $$;

-- Foam/Ledger.lean
CREATE TABLE IF NOT EXISTS foam.charge (
  id       bigserial PRIMARY KEY,
  observer uuid NOT NULL
    CHECK (observer <> '00000000-0000-0000-0000-000000000000'),
  source   uuid NOT NULL DEFAULT '00000000-0000-0000-0000-000000000000',
  ctx      uuid NOT NULL,
  sym      int  NOT NULL,
  delta    int  NOT NULL
);
-- Foam/Seat/Signed.lean
-- Foam/Ledger.lean
CREATE INDEX IF NOT EXISTS foam_charge_ctx ON foam.charge (observer, ctx, sym);

-- Foam/Engine/Summary.lean
CREATE INDEX IF NOT EXISTS foam_charge_ctx_id ON foam.charge (ctx, id) INCLUDE (observer, sym, delta);

-- Foam/Seat/Characters.lean
-- Foam/Engine/Summary.lean
-- Foam/Maintenance.lean
CREATE TABLE IF NOT EXISTS foam.held (
  observer uuid NOT NULL,
  ctx uuid   NOT NULL,
  sym int    NOT NULL,
  n   bigint NOT NULL,
  bal bigint NOT NULL,
  re  bigint NOT NULL,
  im  bigint NOT NULL,
  alt bigint NOT NULL,
  PRIMARY KEY (observer, ctx, sym)
);

-- Foam/Engine/Summary.lean
CREATE TABLE IF NOT EXISTS foam.sweep (
  one       boolean PRIMARY KEY DEFAULT true CHECK (one),
  watermark bigint  NOT NULL DEFAULT 0
);
INSERT INTO foam.sweep (one, watermark) VALUES (true, 0) ON CONFLICT DO NOTHING;

CREATE OR REPLACE FUNCTION foam.bytes(txt text) RETURNS int[] LANGUAGE plpgsql IMMUTABLE AS $$
  DECLARE bin bytea := convert_to(txt,'UTF8'); r int[] := '{}'; i int;
  BEGIN FOR i IN 0..octet_length(bin)-1 LOOP r := r||get_byte(bin,i); END LOOP; RETURN r; END; $$;

CREATE OR REPLACE FUNCTION foam.text(ints int[]) RETURNS text LANGUAGE plpgsql IMMUTABLE AS $$
  DECLARE bin bytea := ''; v int;
  BEGIN FOREACH v IN ARRAY coalesce(ints,'{}') LOOP bin := bin||set_byte('\x00'::bytea,0,v); END LOOP;
        RETURN convert_from(bin,'UTF8'); END; $$;

-- Foam/Engine/Generator.lean
CREATE OR REPLACE FUNCTION foam.hw_random() RETURNS double precision LANGUAGE sql AS
  $$ SELECT (('x'||encode(gen_random_bytes(7),'hex'))::bit(56)::bigint)::double precision / 72057594037927936.0 $$;

-- Foam/Engine/Stream.lean; Foam/Engine/Codec.lean; Foam/Seat/Signed.lean
CREATE OR REPLACE FUNCTION foam.ingest_step(carry int[], bytes int[], kmax int DEFAULT 7,
                                            obs uuid DEFAULT foam.bench(),
                                            from_source uuid DEFAULT foam.root()) RETURNS int[]
  LANGUAGE plpgsql AS $$
  DECLARE all_b int[] := coalesce(carry,'{}') || coalesce(bytes,'{}');
          start_i int := coalesce(array_length(carry,1),0) + 1;
          n int := coalesce(array_length(all_b,1),0);
  BEGIN
    INSERT INTO foam.charge (observer, source, ctx, sym, delta)
    SELECT obs, from_source,
           foam.caddr(CASE WHEN j = 0 THEN '{}'::int[] ELSE all_b[i-j : i-1] END), all_b[i], 1
    FROM generate_series(start_i, n) AS i
    CROSS JOIN LATERAL generate_series(0, least(kmax, i - 1)) AS j
    ORDER BY i, j;
    RETURN all_b[greatest(n - kmax + 1, 1) : n];
  END; $$;

-- Foam/Engine/Summary.lean
CREATE OR REPLACE FUNCTION foam.depth(seed int[], kmax int DEFAULT 7, obs uuid DEFAULT foam.bench()) RETURNS int
  LANGUAGE plpgsql STABLE AS $$
  DECLARE l int := coalesce(array_length(seed,1),0); j int; c int[]; cid uuid; tot bigint;
          anc uuid[] := foam.ancestry(obs);
  BEGIN
    FOR j IN REVERSE least(kmax,l)..1 LOOP
      c := seed[l-j+1 : l]; cid := foam.caddr(c);
      SELECT coalesce(sum(b) FILTER (WHERE b > 0), 0) INTO tot FROM (
        SELECT coalesce(h.bal,0) + coalesce(t.bal,0) AS b
        FROM (SELECT sym, sum(bal)::bigint AS bal FROM foam.held
              WHERE ctx = cid AND observer = ANY(anc) GROUP BY sym) h
        FULL JOIN (SELECT sym, sum(delta) AS bal FROM foam.charge
                   WHERE ctx = cid AND observer = ANY(anc)
                     AND id > (SELECT watermark FROM foam.sweep)
                   GROUP BY sym) t USING (sym)
      ) z;
      IF tot > 0 THEN RETURN j; END IF;
    END LOOP;
    RETURN 0;
  END; $$;

CREATE OR REPLACE FUNCTION foam.outcome(seed int[] DEFAULT '{}', min_depth int DEFAULT 1, kmax int DEFAULT 7,
                                        obs uuid DEFAULT foam.bench()) RETURNS text
  LANGUAGE sql STABLE AS
  $$ SELECT CASE WHEN foam.depth(seed, kmax, obs) >= min_depth THEN 'speak' ELSE 'yield' END $$;

-- Foam/Engine/Spectrum.lean
CREATE OR REPLACE FUNCTION foam.align(tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT CASE ((tk % 4) + 4) % 4 WHEN 0 THEN re WHEN 1 THEN im WHEN 2 THEN -re ELSE -im END $$;

-- Foam/Engine/Spectrum.lean
CREATE OR REPLACE FUNCTION foam.born(tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT foam.align(tk, re, im) * foam.align(tk, re, im) $$;

-- Foam/Seat/Signature.lean
CREATE OR REPLACE FUNCTION foam.normK(kappa bigint, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS
  $$ SELECT re * re - kappa * (im * im) $$;

-- Foam/Seat/Signature.lean
CREATE OR REPLACE FUNCTION foam.born_kappa(kappa int, tk int, re bigint, im bigint) RETURNS bigint
  LANGUAGE sql IMMUTABLE AS $$
    SELECT CASE kappa
      WHEN -1 THEN foam.born(tk, re, im)
      WHEN  0 THEN re * re
      ELSE greatest(re * re - im * im, 0)
    END
  $$;

-- Foam/Engine/Spectrum.lean
CREATE OR REPLACE FUNCTION foam.born_audit() RETURNS bigint
  LANGUAGE sql STABLE AS $$
    SELECT count(*)
    FROM generate_series(-8, 8) re CROSS JOIN generate_series(-8, 8) im
    WHERE foam.align(0, re, im) <> re
       OR foam.align(1, re, im) <> foam.align(0, im, -re)
       OR foam.align(2, re, im) <> foam.align(1, im, -re)
       OR foam.align(3, re, im) <> foam.align(2, im, -re)
       OR foam.born(0, re, im) + foam.born(1, re, im) + foam.born(2, re, im) + foam.born(3, re, im)
          <> 2 * (re * re + im * im)
       OR least(foam.born(0, re, im), foam.born(1, re, im), foam.born(2, re, im), foam.born(3, re, im)) < 0
  $$;

-- Foam/Seat/Signature.lean
CREATE OR REPLACE FUNCTION foam.kparseval_audit(kappa bigint) RETURNS bigint
  LANGUAGE sql STABLE AS $$
    SELECT count(*)
    FROM generate_series(-4, 4) a CROSS JOIN generate_series(-4, 4) b
         CROSS JOIN generate_series(-4, 4) c CROSS JOIN generate_series(-4, 4) d
    WHERE (a * c - kappa * (b * d)) * (a * c - kappa * (b * d))
            - kappa * ((a * d - b * c) * (a * d - b * c))
          <> (a * a - kappa * (b * b)) * (c * c - kappa * (d * d))
  $$;

-- Foam/Engine/Summary.lean
-- Foam/Engine/Spectrum.lean
-- Foam/Engine/Drain.lean
-- Foam/Scar.lean
-- Foam/Maintenance.lean
CREATE OR REPLACE FUNCTION foam.speak(seed int[] DEFAULT '{}', kmax int DEFAULT 7, max_steps int DEFAULT 600,
                           stop int DEFAULT NULL, obs uuid DEFAULT foam.bench(), kappa int DEFAULT -1) RETURNS int[]
  LANGUAGE plpgsql SET work_mem = '256MB' AS $$
  DECLARE cb int[] := coalesce(seed,'{}'); out int[] := '{}'; k int := 0; j int; l int; c int[]; cid uuid;
          tot bigint; thr double precision; acc bigint; got boolean; tk int;
          rests int := 0; wounded int[]; w int; syms int[]; ws bigint[]; i int; said int;
          phase0 int := coalesce(array_length(seed,1),0) % 4;
          anc uuid[] := foam.ancestry(obs);
  BEGIN
    WHILE k < max_steps LOOP
      tk := (phase0 + k) % 4;
      got := false; l := coalesce(array_length(cb,1),0);
      FOR j IN REVERSE least(kmax,l)..0 LOOP
        IF j = 0 THEN c := '{}'; ELSE c := cb[l-j+1 : l]; END IF;
        cid := foam.caddr(c);
        -- Foam/Engine/Chirality.lean
        SELECT coalesce(sum(z.w) FILTER (WHERE z.bal > 0 AND z.w > 0), 0),
               coalesce(array_agg(z.sym ORDER BY z.w DESC) FILTER (WHERE z.bal > 0 AND z.w > 0), '{}'),
               coalesce(array_agg(z.w   ORDER BY z.w DESC) FILTER (WHERE z.bal > 0 AND z.w > 0), '{}'),
               coalesce(array_agg(z.sym) FILTER (WHERE z.bal < 0), '{}')
          INTO tot, syms, ws, wounded
          FROM (
            -- Foam/Seat/Born.lean
            SELECT sym, bal, foam.born_kappa(kappa, tk, rre, rim) AS w
            FROM (
              SELECT sym, sum(bal)::bigint AS bal,
                     sum(CASE ((nn + 3) % 4) WHEN 0 THEN  re WHEN 1 THEN im WHEN 2 THEN -re ELSE -im END)::bigint AS rre,
                     sum(CASE ((nn + 3) % 4) WHEN 0 THEN -im WHEN 1 THEN re WHEN 2 THEN  im ELSE -re END)::bigint AS rim
              FROM (
                SELECT coalesce(h.sym, t.sym) AS sym,
                       coalesce(h.bal,0) + coalesce(t.bal,0) AS bal,
                       coalesce(h.re,0)  + coalesce(t.re,0)  AS re,
                       coalesce(h.im,0)  + coalesce(t.im,0)  AS im,
                       coalesce(h.n,0)   + coalesce(t.tn,0)  AS nn
                FROM (SELECT observer, sym, n, bal, re, im
                      FROM foam.held WHERE ctx = cid AND observer = ANY(anc)) h
                FULL JOIN (
                  SELECT e.observer, e.sym, count(*) AS tn, sum(e.delta) AS bal,
                         sum(e.delta * CASE ((coalesce(h2.n,0) + e.k2) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
                         sum(e.delta * CASE ((coalesce(h2.n,0) + e.k2) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im
                  FROM (SELECT observer, sym, delta,
                               row_number() OVER (PARTITION BY observer, sym ORDER BY id) - 1 AS k2
                        FROM foam.charge WHERE ctx = cid AND observer = ANY(anc)
                          AND id > (SELECT watermark FROM foam.sweep)) e
                  LEFT JOIN foam.held h2 ON h2.observer = e.observer AND h2.ctx = cid AND h2.sym = e.sym
                  GROUP BY e.observer, e.sym
                ) t ON t.observer = h.observer AND t.sym = h.sym
              ) absf
              GROUP BY sym
            ) recf
          ) z;
        FOREACH w IN ARRAY wounded LOOP PERFORM foam.settle(cid, w, obs); END LOOP;
        IF tot > 0 THEN
          thr := foam.hw_random() * tot; acc := 0;
          FOR i IN 1..coalesce(array_length(syms,1),0) LOOP
            acc := acc + ws[i];
            IF acc >= thr THEN
              out := out || syms[i]; cb := cb || syms[i]; got := true; said := syms[i];
              INSERT INTO foam.charge (observer, ctx, sym, delta) VALUES (obs, cid, syms[i], -1);
              EXIT;
            END IF;
          END LOOP;
        END IF;
        EXIT WHEN got;
      END LOOP;
      IF got AND said = stop THEN RETURN out; END IF;
      IF got THEN rests := 0; ELSE rests := rests + 1; END IF;
      EXIT WHEN rests >= 4;
      k := k + 1;
    END LOOP;
    RETURN out;
  END; $$;

-- Foam/Scar.lean
-- Foam/Maintenance.lean
CREATE OR REPLACE FUNCTION foam.settle(c uuid, s int, obs uuid DEFAULT foam.bench()) RETURNS void
  LANGUAGE plpgsql AS $$
  DECLARE t uuid; b bigint; run bigint := 0;
  BEGIN
    PERFORM pg_advisory_xact_lock(hashtext('foam.settle'), 0);
    FOREACH t IN ARRAY foam.lineage(obs) LOOP
      SELECT coalesce(sum(delta), 0) INTO b FROM foam.charge
       WHERE ctx = c AND sym = s AND observer = t;
      run := run + b;
      IF run < 0 THEN
        INSERT INTO foam.charge (observer, ctx, sym, delta) SELECT t, c, s, 1 FROM generate_series(1, -run);
        run := 0;
      END IF;
    END LOOP;
  END; $$;

-- Foam/Scar.lean
CREATE OR REPLACE FUNCTION foam.settle_sweep(obs uuid DEFAULT foam.bench()) RETURNS bigint
  LANGUAGE plpgsql AS $$
  DECLARE n bigint := 0; rec record; anc uuid[] := foam.ancestry(obs);
  BEGIN
    PERFORM pg_advisory_xact_lock(hashtext('foam.settle'), 0);
    FOR rec IN SELECT ctx, sym FROM foam.charge
               WHERE observer = ANY(anc) GROUP BY ctx, sym HAVING sum(delta) < 0 LOOP
      PERFORM foam.settle(rec.ctx, rec.sym, obs);
      n := n + 1;
    END LOOP;
    RETURN n;
  END; $$;

-- Foam/Engine/Summary.lean
-- Foam/Maintenance.lean
CREATE OR REPLACE FUNCTION foam.sweep_step(hi bigint DEFAULT NULL, batch int DEFAULT 200000) RETURNS bigint
  LANGUAGE plpgsql SET work_mem = '256MB' AS $$
  DECLARE wm bigint; top bigint; folded bigint; last_id bigint;
  BEGIN
    IF NOT pg_try_advisory_xact_lock(hashtext('foam.sweep'), 0) THEN RETURN -1; END IF;
    SELECT watermark INTO wm FROM foam.sweep;
    top := coalesce(hi, (SELECT max(id) FROM foam.charge));
    IF top IS NULL OR top <= wm THEN RETURN 0; END IF;

    WITH lim AS (
      SELECT id, observer, ctx, sym, delta FROM foam.charge
      WHERE id > wm AND id <= top ORDER BY id LIMIT batch
    ), b AS (
      SELECT observer, ctx, sym, delta,
             row_number() OVER (PARTITION BY observer, ctx, sym ORDER BY id) - 1 AS k
      FROM lim
    ), g AS (
      SELECT b.observer, b.ctx, b.sym, count(*) AS dn, sum(b.delta) AS dbal,
             sum(b.delta * CASE ((coalesce(h.n,0) + b.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS dre,
             sum(b.delta * CASE ((coalesce(h.n,0) + b.k) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS dim,
             sum(b.delta * CASE ((coalesce(h.n,0) + b.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN 1 ELSE -1 END) AS dalt
      FROM b LEFT JOIN foam.held h ON h.observer = b.observer AND h.ctx = b.ctx AND h.sym = b.sym
      GROUP BY b.observer, b.ctx, b.sym, h.n
    ), up AS (
      INSERT INTO foam.held (observer, ctx, sym, n, bal, re, im, alt)
      SELECT observer, ctx, sym, dn, dbal, dre, dim, dalt FROM g
      ON CONFLICT (observer, ctx, sym) DO UPDATE SET
        n   = foam.held.n   + EXCLUDED.n,
        bal = foam.held.bal + EXCLUDED.bal,
        re  = foam.held.re  + EXCLUDED.re,
        im  = foam.held.im  + EXCLUDED.im,
        alt = foam.held.alt + EXCLUDED.alt
      RETURNING 1
    )
    SELECT count(*), max(id) INTO folded, last_id FROM lim;

    UPDATE foam.sweep SET watermark = CASE WHEN folded < batch THEN top ELSE last_id END;
    RETURN folded;
  END; $$;

CREATE OR REPLACE FUNCTION foam.sweep_fenced(batch int DEFAULT 200000) RETURNS bigint
  LANGUAGE plpgsql AS $$
  DECLARE hi bigint;
  BEGIN
    LOCK TABLE foam.charge IN EXCLUSIVE MODE;
    SELECT max(id) INTO hi FROM foam.charge;
    RETURN foam.sweep_step(hi, batch);
  END; $$;

-- Foam/Held.lean
-- Foam/Engine/Summary.lean
CREATE OR REPLACE FUNCTION foam.held_audit(obs uuid DEFAULT foam.bench()) RETURNS bigint
  LANGUAGE sql STABLE SET work_mem = '256MB' AS $$
  WITH live AS (
    SELECT observer, ctx, sym, count(*) AS n, sum(delta) AS bal,
           sum(delta * CASE ((occ - 1) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
           sum(delta * CASE ((occ - 1) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im,
           sum(delta * CASE ((occ - 1) % 4) WHEN 0 THEN 1 WHEN 2 THEN 1 ELSE -1 END) AS alt
    FROM (SELECT observer, ctx, sym, delta,
                 row_number() OVER (PARTITION BY observer, ctx, sym ORDER BY id) AS occ
          FROM foam.charge WHERE observer = ANY(foam.ancestry(obs))) e
    GROUP BY observer, ctx, sym
  ), tail AS (
    SELECT e.observer, e.ctx, e.sym, count(*) AS n, sum(e.delta) AS bal,
           sum(e.delta * CASE ((coalesce(h.n,0) + e.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN -1 ELSE 0 END) AS re,
           sum(e.delta * CASE ((coalesce(h.n,0) + e.k) % 4) WHEN 1 THEN 1 WHEN 3 THEN -1 ELSE 0 END) AS im,
           sum(e.delta * CASE ((coalesce(h.n,0) + e.k) % 4) WHEN 0 THEN 1 WHEN 2 THEN 1 ELSE -1 END) AS alt
    FROM (SELECT observer, ctx, sym, delta,
                 row_number() OVER (PARTITION BY observer, ctx, sym ORDER BY id) - 1 AS k
          FROM foam.charge WHERE observer = ANY(foam.ancestry(obs))
            AND id > (SELECT watermark FROM foam.sweep)) e
    LEFT JOIN foam.held h ON h.observer = e.observer AND h.ctx = e.ctx AND h.sym = e.sym
    GROUP BY e.observer, e.ctx, e.sym, h.n
  ), merged AS (
    SELECT coalesce(h.observer, t.observer) AS observer,
           coalesce(h.ctx, t.ctx) AS ctx, coalesce(h.sym, t.sym) AS sym,
           coalesce(h.n,0) + coalesce(t.n,0) AS n, coalesce(h.bal,0) + coalesce(t.bal,0) AS bal,
           coalesce(h.re,0) + coalesce(t.re,0) AS re, coalesce(h.im,0) + coalesce(t.im,0) AS im,
           coalesce(h.alt,0) + coalesce(t.alt,0) AS alt
    FROM (SELECT observer, ctx, sym, n, bal, re, im, alt FROM foam.held
          WHERE observer = ANY(foam.ancestry(obs))) h
    FULL JOIN tail t ON t.observer = h.observer AND t.ctx = h.ctx AND t.sym = h.sym
  )
  SELECT count(*) FROM (
    (TABLE live EXCEPT TABLE merged) UNION ALL (TABLE merged EXCEPT TABLE live)
  ) d $$;

-- Foam/Seat/Signed.lean
CREATE OR REPLACE FUNCTION foam.healthcheck() RETURNS TABLE(issue text) LANGUAGE sql STABLE AS $$
  SELECT 'overloaded: foam.' || p.proname || ' — ' || count(*) || ' implementations; DROP the stale signature'
  FROM pg_proc p JOIN pg_namespace n ON n.oid = p.pronamespace
  WHERE n.nspname = 'foam'
  GROUP BY p.proname HAVING count(*) > 1
  UNION ALL
  SELECT 'foam.charge is missing its source column (the input signature)'
  WHERE NOT EXISTS (
    SELECT 1 FROM information_schema.columns
    WHERE table_schema = 'foam' AND table_name = 'charge' AND column_name = 'source'
  )
$$;

-- Foam/Engine/Drain.lean
-- Foam/Scar.lean
-- Foam/Engine/Summary.lean
CREATE OR REPLACE FUNCTION foam.stats()
  RETURNS TABLE(events bigint, heard bigint, spoken bigint, net bigint, residual bigint,
                notes bigint, outstanding bigint, contexts bigint, live_continuations bigint,
                held bigint, tail bigint)
  LANGUAGE sql STABLE SET work_mem = '512MB' AS $$
    WITH g AS (
      SELECT ctx, sym,
             sum(delta)                         AS s,
             count(*)                           AS n,
             count(*) FILTER (WHERE delta = -1) AS neg
      FROM foam.charge
      GROUP BY ctx, sym
    )
    SELECT
      coalesce(sum(n), 0)::bigint,
      coalesce(sum(n - neg) FILTER (WHERE ctx = foam.caddr('{}')), 0)::bigint,
      coalesce(sum(neg), 0)::bigint,
      coalesce(sum(s), 0)::bigint,
      coalesce(sum(s) FILTER (WHERE s > 0), 0)::bigint,
      (count(*) FILTER (WHERE s < 0))::bigint,
      coalesce(-sum(s) FILTER (WHERE s < 0), 0)::bigint,
      (count(DISTINCT ctx))::bigint,
      (count(*) FILTER (WHERE s > 0))::bigint,
      (SELECT count(*) FROM foam.held)::bigint,
      (SELECT count(*) FROM foam.charge c2
        WHERE c2.id > (SELECT watermark FROM foam.sweep))::bigint
    FROM g
  $$;

-- Foam/Ledger.lean
CREATE OR REPLACE FUNCTION foam.recorded(obs uuid DEFAULT foam.bench()) RETURNS text LANGUAGE sql STABLE AS
  $$ SELECT coalesce(foam.text(array_agg(sym ORDER BY id)), '')
     FROM foam.charge
     WHERE ctx = foam.caddr('{}') AND delta = 1 AND observer = ANY(foam.ancestry(obs)) $$;
