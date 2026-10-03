/*
 * Red Rogue save converter engine. No dependencies; runs in a browser (window.RRSaveConvert)
 * and in Node (module.exports) so the patch page and the regression tests run the same code.
 *
 * A "package" (built by tools/save_compat/build_package.py) carries everything for one target
 * build: its schema, the schemas of every source it accepts, how to recognise those sources,
 * the migrations between them, and (when recovery is offered) a verified post-reset template.
 *
 *   identify(save, pkg)                       -> what the save is, or why it can't be read
 *   sourceFromRom(romSha256, pkg)             -> the untagged source a player's old ROM identifies
 *   convert(save, pkg, {source, mode})        -> {ok, bytes, report} or {ok: false, reason}
 *
 * Saves are raw 32 KiB MBC3 SRAM (.sav / .srm). Every function takes and returns Uint8Arrays and
 * never modifies its input.
 */
(function (root) {
  "use strict";

  var SRAM_SIZE = 0x8000;
  var BANK_SIZE = 0x2000;
  var MAGIC = [0x52, 0x52, 0x53, 0x47]; // "RRSG"

  function fail(code, message) {
    return { ok: false, code: code, reason: message };
  }

  function offsetOf(bank, address) {
    return bank * BANK_SIZE + (parseInt(address, 16) - 0xa000);
  }

  function sum8(bytes, start, length) {
    var d = 0;
    for (var i = 0; i < length; i++) d = (d + bytes[start + i]) & 0xff;
    return (~d) & 0xff;
  }

  function sramField(schema, label) {
    for (var i = 0; i < schema.sram.length; i++) if (schema.sram[i].label === label) return schema.sram[i];
    return null;
  }

  function wramField(schema, label) {
    for (var i = 0; i < schema.saved_wram.length; i++) if (schema.saved_wram[i].label === label) return schema.saved_wram[i];
    return null;
  }

  // Byte offset in the .sav of a saved-WRAM field (it lives inside one of the main save blocks).
  function wramOffset(schema, label) {
    var f = wramField(schema, label);
    if (!f) return -1;
    var block = sramField(schema, f.block);
    return offsetOf(block.bank, block.address) + f.offset;
  }

  function readHeader(save) {
    var o = offsetOf(1, "a040");
    var bytes = Array.prototype.slice.call(save, o, o + 8);
    var magic = bytes[0] === MAGIC[0] && bytes[1] === MAGIC[1] && bytes[2] === MAGIC[2] && bytes[3] === MAGIC[3];
    if (!magic) return { present: false };
    var id = bytes[4] | (bytes[5] << 8);
    var inverse = bytes[6] | (bytes[7] << 8);
    return { present: true, valid: ((~id) & 0xffff) === inverse, schemaId: id };
  }

  function writeHeader(save, schemaId) {
    var o = offsetOf(1, "a040");
    var inverse = (~schemaId) & 0xffff;
    var bytes = MAGIC.concat([schemaId & 0xff, schemaId >> 8, inverse & 0xff, inverse >> 8]);
    for (var i = 0; i < 8; i++) save[o + i] = bytes[i];
  }

  function checksumStatus(save, schema) {
    var out = {};
    schema.checksums.forEach(function (c) {
      var start = offsetOf(c.bank, c.start);
      var at = offsetOf(c.at_bank, c.at);
      out[c.name] = sum8(save, start, c.length) === save[at];
    });
    return out;
  }

  function recomputeChecksums(save, schema, names) {
    schema.checksums.forEach(function (c) {
      if (names && names.indexOf(c.name) < 0) return;
      save[offsetOf(c.at_bank, c.at)] = sum8(save, offsetOf(c.bank, c.start), c.length);
    });
  }

  // Structural checks a real save from this schema always passes. A failure means corrupt data,
  // or a save from some other layout that happens to share a checksum.
  function boundsProblems(save, schema) {
    var problems = [];
    function byte(label) {
      var o = wramOffset(schema, label);
      return o < 0 ? null : save[o];
    }
    var name = wramOffset(schema, "wPlayerName");
    var terminated = false;
    for (var i = 0; i < 11; i++) if (save[name + i] === 0x50) terminated = true;
    if (!terminated || save[name] === 0x50) problems.push("the player name is missing or unterminated");
    var party = byte("wPartyCount");
    if (party === null || party > 6) problems.push("party count " + party + " is more than 6");
    else {
      var species = wramOffset(schema, "wPartySpecies");
      if (save[species + party] !== 0xff) problems.push("the party list isn't terminated after " + party + " Pokemon");
    }
    var box = byte("wBoxCount");
    if (box === null || box > 20) problems.push("current box count " + box + " is more than 20");
    var boxNum = byte("wCurrentBoxNum");
    if (boxNum !== null && (boxNum & 0x7f) >= 12) problems.push("current box number " + (boxNum & 0x7f) + " is past box 12");
    return problems;
  }

  // What a save is, according to this package. Never trusts a header alone: the main checksum
  // and the structure must agree with the schema it names.
  function identify(save, pkg) {
    if (!(save instanceof Uint8Array)) return fail("type", "expected the save's bytes");
    if (save.length !== SRAM_SIZE) {
      if (save.length > SRAM_SIZE && save.length <= SRAM_SIZE + 64)
        return fail("wrapped", "This file is " + save.length + " bytes: an emulator added extra data after the save. " +
          "Export a raw 32 KB .sav (in mGBA: File > Export save; most emulators have a 'raw' or '.sav' option).");
      if (save.length > 0x10000)
        return fail("state", "This looks like an emulator save state, not a battery save. Use the game's own save " +
          "file (.sav or .srm), not a state (.ss1, .sn1, .state, ...).");
      return fail("size", "A Red Rogue save is exactly 32768 bytes; this file is " + save.length + ".");
    }
    var header = readHeader(save);
    if (header.present) {
      if (!header.valid) return fail("header", "The save's header is damaged, so its layout can't be trusted.");
      var schema = pkg.schemas[String(header.schemaId)];
      if (!schema) return fail("unknown_schema", "This save uses save format " + header.schemaId +
        ", which this build's converter doesn't know. Pick a newer build on this page, or ask the developers.");
      return checkAgainst(save, schema, { tagged: true, source: String(header.schemaId) });
    }
    return { ok: true, tagged: false, needsRom: true,
      reason: "This save has no format tag, so it comes from an older build. Pick the patched ROM you played it with " +
        "so the converter can tell which build that was." };
  }

  function checkAgainst(save, schema, result) {
    var sums = checksumStatus(save, schema);
    if (!sums.main) return fail("checksum", "The save's main checksum doesn't match: the file is damaged, or it isn't " +
      "from the build you picked.");
    var problems = boundsProblems(save, schema);
    if (problems.length) return fail("bounds", "The save doesn't look like a Red Rogue save from that build: " + problems.join("; ") + ".");
    result.ok = true;
    result.checksums = sums;
    return result;
  }

  function sourceFromRom(romSha256, pkg) {
    var hash = String(romSha256).toLowerCase();
    for (var i = 0; i < pkg.sources.length; i++) {
      var s = pkg.sources[i];
      if (s.rom_sha256.indexOf(hash) >= 0) return s;
    }
    return null;
  }

  function findMigration(pkg, from) {
    for (var i = 0; i < pkg.migrations.length; i++) if (pkg.migrations[i].from === from) return pkg.migrations[i];
    return null;
  }

  // Migration steps, by name. Each takes (bytes, fromSchema, toSchema) and edits the copy in place,
  // or returns a refusal string. They are explicit on purpose: a matching label name never proves
  // two fields mean the same thing.
  var STEPS = {
    // Same layout and meaning (tools/save_schema.py diff --ignore-header said identical): only the
    // header is new, and it sits in padding no checksum covers.
    tag: function () { return null; }
  };

  function convert(save, pkg, options) {
    options = options || {};
    var mode = options.mode || "continue";
    var target = pkg.target;
    var targetSchema = pkg.schemas[String(target.schema)];
    var from;
    var id = identify(save, pkg);
    if (!id.ok) return id;
    if (id.tagged) from = id.source;
    else {
      if (!options.source) return fail("needs_rom", id.reason);
      from = options.source;
      var sourceSchema = pkg.schemas[from];
      if (!sourceSchema) return fail("unknown_source", "This converter can't read saves from " + from + ".");
      var check = checkAgainst(save, sourceSchema, { tagged: false, source: from });
      if (!check.ok) return check;
    }
    var out = new Uint8Array(save);
    var report = { from: from, to: String(target.schema), mode: mode, steps: [] };

    if (mode === "continue") {
      if (from === String(target.schema)) {
        report.steps.push("already in this build's save format; nothing to change");
      } else {
        // Follow migrations one schema at a time, so a save that skipped releases still arrives.
        var at = from, seen = {};
        while (at !== String(target.schema)) {
          var migration = findMigration(pkg, at);
          if (!migration || seen[at])
            return fail("no_migration", "There's no way to carry this save into this build" +
              (pkg.recovery ? ". A recovery (keeping permanent progress) may be possible." : "."));
          seen[at] = true;
          for (var i = 0; i < migration.steps.length; i++) {
            var step = STEPS[migration.steps[i]];
            if (!step) return fail("bad_package", "Unknown migration step " + migration.steps[i] + ".");
            var refusal = step(out, pkg.schemas[at], pkg.schemas[migration.to]);
            if (refusal) return fail("refused", refusal);
            report.steps.push(at + " -> " + migration.to + ": " + migration.steps[i]);
          }
          at = migration.to;
        }
        writeHeader(out, target.schema);
        report.steps.push("wrote save format " + target.schema);
      }
    } else if (mode === "recovery") {
      var made = recover(save, pkg, from, report);
      if (!made.ok) return made;
      out = made.bytes;
    } else {
      return fail("mode", "Unknown conversion mode " + mode + ".");
    }

    var verify = identify(out, pkg);
    if (!verify.ok || !verify.tagged || verify.source !== String(target.schema))
      return fail("verify", "The converted save failed its own check (" + (verify.reason || "wrong format") + "). Nothing was changed.");
    report.checksums = verify.checksums;
    return { ok: true, bytes: out, report: report };
  }

  // Recovery: the target's verified post-reset Dorm save, with the source's permanent progress
  // copied in. Only fields listed in pkg.recovery.keep are carried, each by label, and only when
  // source and target agree on its size.
  function recover(save, pkg, from, report) {
    var r = pkg.recovery;
    if (!r || !r.template) return fail("no_recovery", "Recovery isn't offered for this build yet.");
    var sourceSchema = pkg.schemas[from];
    var targetSchema = pkg.schemas[String(pkg.target.schema)];
    var out = base64Bytes(r.template);
    if (out.length !== SRAM_SIZE) return fail("bad_package", "The recovery template is damaged.");
    var kept = [], lost = [];
    function copy(srcOff, dstOff, size) { for (var i = 0; i < size; i++) out[dstOff + i] = save[srcOff + i]; }
    r.keep_sram.forEach(function (label) {
      var a = sramField(sourceSchema, label), b = sramField(targetSchema, label);
      if (!a || !b || a.size !== b.size) { lost.push(label); return; }
      copy(offsetOf(a.bank, a.address), offsetOf(b.bank, b.address), a.size);
      kept.push(label);
    });
    r.keep_wram.forEach(function (label) {
      var a = wramField(sourceSchema, label), b = wramField(targetSchema, label);
      if (!a || !b || a.size !== b.size) { lost.push(label); return; }
      copy(wramOffset(sourceSchema, label), wramOffset(targetSchema, label), a.size);
      kept.push(label);
    });
    (r.keep_event_bytes || []).forEach(function (range) {
      var a = wramOffset(sourceSchema, "wEventFlags"), b = wramOffset(targetSchema, "wEventFlags");
      copy(a + range[0], b + range[0], range[1] - range[0]);
    });
    recomputeChecksums(out, targetSchema, r.recompute_checksums);
    writeHeader(out, pkg.target.schema);
    report.kept = kept;
    report.lost = lost.concat(r.always_lost || []);
    report.steps.push("started from the post-reset Dorm template", "copied " + kept.length + " permanent fields");
    return { ok: true, bytes: out };
  }

  function base64Bytes(text) {
    if (typeof atob === "function") {
      var bin = atob(text), out = new Uint8Array(bin.length);
      for (var i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
      return out;
    }
    return new Uint8Array(Buffer.from(text, "base64"));
  }

  var api = {
    SRAM_SIZE: SRAM_SIZE,
    identify: identify,
    sourceFromRom: sourceFromRom,
    convert: convert,
    readHeader: readHeader,
    checksumStatus: checksumStatus,
    _internal: { sum8: sum8, writeHeader: writeHeader, recomputeChecksums: recomputeChecksums, wramOffset: wramOffset,
      offsetOf: offsetOf, boundsProblems: boundsProblems, STEPS: STEPS }
  };
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.RRSaveConvert = api;
})(typeof self !== "undefined" ? self : this);
;(function (root) {
  var api = (typeof module === "object" && module.exports) ? module.exports : root.RRSaveConvert;
  api.PACKAGE = {"format":1,"target":{"schema":1},"schemas":{"1":{"schema_id":1,"source":{"sym":"pokeblue_debug.sym","commit":null},"header":{"bank":1,"address":"a040"},"checksums":[{"name":"main","bank":1,"start":"a4f4","length":3821,"at_bank":1,"at":"b3e1","optional":false},{"name":"boxes_1_to_6","bank":2,"start":"a000","length":6732,"at_bank":2,"at":"ba4c","optional":false},{"name":"box1","bank":2,"start":"a000","length":1122,"at_bank":2,"at":"ba4d","optional":false},{"name":"box2","bank":2,"start":"a462","length":1122,"at_bank":2,"at":"ba4e","optional":false},{"name":"box3","bank":2,"start":"a8c4","length":1122,"at_bank":2,"at":"ba4f","optional":false},{"name":"box4","bank":2,"start":"ad26","length":1122,"at_bank":2,"at":"ba50","optional":false},{"name":"box5","bank":2,"start":"b188","length":1122,"at_bank":2,"at":"ba51","optional":false},{"name":"box6","bank":2,"start":"b5ea","length":1122,"at_bank":2,"at":"ba52","optional":false},{"name":"boxes_7_to_12","bank":3,"start":"a000","length":6732,"at_bank":3,"at":"ba4c","optional":false},{"name":"box7","bank":3,"start":"a000","length":1122,"at_bank":3,"at":"ba4d","optional":false},{"name":"box8","bank":3,"start":"a462","length":1122,"at_bank":3,"at":"ba4e","optional":false},{"name":"box9","bank":3,"start":"a8c4","length":1122,"at_bank":3,"at":"ba4f","optional":false},{"name":"box10","bank":3,"start":"ad26","length":1122,"at_bank":3,"at":"ba50","optional":false},{"name":"box11","bank":3,"start":"b188","length":1122,"at_bank":3,"at":"ba51","optional":false},{"name":"box12","bank":3,"start":"b5ea","length":1122,"at_bank":3,"at":"ba52","optional":false},{"name":"final_team_header","bank":1,"start":"b3e2","length":10,"at_bank":1,"at":"b3ec","optional":true},{"name":"final_team_record0","bank":1,"start":"b3ed","length":406,"at_bank":1,"at":"b3e8","optional":true},{"name":"final_team_record1","bank":1,"start":"b583","length":406,"at_bank":1,"at":"b3e9","optional":true},{"name":"final_team_record2","bank":1,"start":"b719","length":406,"at_bank":1,"at":"b3ea","optional":true},{"name":"final_team_record3","bank":1,"start":"b8af","length":406,"at_bank":1,"at":"b3eb","optional":true}],"sram":[{"label":"sSpriteBuffer0","bank":0,"address":"a000","size":392},{"label":"sSpriteBuffer1","bank":0,"address":"a188","size":392},{"label":"sSpriteBuffer2","bank":0,"address":"a310","size":648},{"label":"sHallOfFame","bank":0,"address":"a598","size":4800},{"label":"sProcCaveStagingBuffer","bank":0,"address":"b858","size":600},{"label":"sProcCemeteryMaps","bank":0,"address":"bab0","size":360},{"label":"sProcCemeteryBallX","bank":0,"address":"bc18","size":4},{"label":"sProcCemeteryBallY","bank":0,"address":"bc1c","size":4},{"label":"sProcCemeteryItem","bank":0,"address":"bc20","size":4},{"label":"sProcCemeteryReady","bank":0,"address":"bc24","size":1},{"label":"sProcCemeteryItemGot","bank":0,"address":"bc25","size":1},{"label":"sProcCemeteryUsedPrefabs","bank":0,"address":"bc26","size":2},{"label":"sProcCemeteryBossSpecies","bank":0,"address":"bc28","size":1},{"label":"sProcCemeteryBossMove","bank":0,"address":"bc29","size":1},{"label":"sProcCaveStagingEntranceY","bank":0,"address":"bc2a","size":1},{"label":"sProcCaveStagingEntranceX","bank":0,"address":"bc2b","size":1},{"label":"sProcCaveStagingExitY","bank":0,"address":"bc2c","size":1},{"label":"sProcCaveStagingExitX","bank":0,"address":"bc2d","size":1},{"label":"sProcCaveStagingBossSprite","bank":0,"address":"bc2e","size":1},{"label":"sProcCaveStagingLadderID","bank":0,"address":"bc2f","size":1},{"label":"sProcCaveStagingLadderOffset","bank":0,"address":"bc30","size":1},{"label":"sProcCaveSignVariant","bank":0,"address":"bc31","size":1},{"label":"sProcCaveEntranceWarpID","bank":0,"address":"bc32","size":1},{"label":"sProcCaveBallsStaged","bank":0,"address":"bc33","size":1},{"label":"sProcCaveBallXY","bank":0,"address":"bc34","size":8},{"label":"sProcCaveBallItems","bank":0,"address":"bc3c","size":4},{"label":"sProcCaveBaked","bank":0,"address":"bc40","size":1},{"label":"sProcForestStagingBuffer","bank":0,"address":"bc41","size":600},{"label":"sProcForestExitI","bank":0,"address":"be99","size":1},{"label":"sProcForestExitEdge","bank":0,"address":"be9a","size":1},{"label":"sProcForestRiverSide","bank":0,"address":"be9b","size":1},{"label":"sProcForestBaked","bank":0,"address":"be9c","size":1},{"label":"sProcForestBossSpecies","bank":0,"address":"be9d","size":1},{"label":"sProcForestBossSprite","bank":0,"address":"be9e","size":1},{"label":"sProcForestBallXY","bank":0,"address":"be9f","size":8},{"label":"sProcForestBallItems","bank":0,"address":"bea7","size":4},{"label":"sProcForestItemGot","bank":0,"address":"beab","size":1},{"label":"sProcForestSignVariant","bank":0,"address":"beac","size":1},{"label":"sProcForestAlgoForce","bank":0,"address":"bead","size":1},{"label":"sProcForestGenScratch","bank":0,"address":"beae","size":81},{"label":"sProcCavePalette","bank":0,"address":"beff","size":1},{"label":"sProcForestPalette","bank":0,"address":"bf00","size":1},{"label":"sProcCemeteryPalette","bank":0,"address":"bf01","size":1},{"label":"sStageEventHideoutX","bank":0,"address":"bf02","size":1},{"label":"sStageEventHideoutY","bank":0,"address":"bf03","size":1},{"label":"sStageEventHideoutAltX","bank":0,"address":"bf04","size":1},{"label":"sStageEventHideoutAltY","bank":0,"address":"bf05","size":1},{"label":"sStageEventSprite6","bank":0,"address":"bf06","size":1},{"label":"sStageEventSprite7","bank":0,"address":"bf07","size":1},{"label":"sStageEventHideoutFloor","bank":0,"address":"bf08","size":1},{"label":"sStolenKind","bank":1,"address":"a000","size":1},{"label":"sStolenRecord","bank":1,"address":"a000","size":1},{"label":"sStolenItem","bank":1,"address":"a001","size":1},{"label":"sStolenBoxMon","bank":1,"address":"a002","size":33},{"label":"sStolenNickname","bank":1,"address":"a023","size":11},{"label":"sStolenOTName","bank":1,"address":"a02e","size":11},{"label":"sStolenRecordEnd","bank":1,"address":"a039","size":7},{"label":"sSaveHeader","bank":1,"address":"a040","size":4},{"label":"sSaveHeaderMagic","bank":1,"address":"a040","size":4},{"label":"sSaveHeaderSchemaID","bank":1,"address":"a044","size":2},{"label":"sSaveHeaderSchemaIDInverse","bank":1,"address":"a046","size":2},{"label":"sSaveHeaderEnd","bank":1,"address":"a048","size":936},{"label":"sRoomOwnedExt","bank":1,"address":"a3f0","size":4},{"label":"sDebugFight2Spec","bank":1,"address":"a3f4","size":1},{"label":"sDebugFight2SpecMagic","bank":1,"address":"a3f4","size":1},{"label":"sDebugFight2PlayerCount","bank":1,"address":"a3f5","size":1},{"label":"sDebugFight2EnemyCount","bank":1,"address":"a3f6","size":1},{"label":"sDebugFight2TrainerClass","bank":1,"address":"a3f7","size":1},{"label":"sDebugFight2AITier","bank":1,"address":"a3f8","size":1},{"label":"sDebugFight2Mons","bank":1,"address":"a3f9","size":72},{"label":"sDebugFight2SpecEnd","bank":1,"address":"a441","size":112},{"label":"sFusionDiagBuf","bank":1,"address":"a441","size":112},{"label":"sTMBitfield","bank":1,"address":"a4b1","size":7},{"label":"sKeyItemsBitfield","bank":1,"address":"a4b8","size":4},{"label":"sKeyItemTiers","bank":1,"address":"a4bc","size":4},{"label":"sRoomFurniture","bank":1,"address":"a4c0","size":2},{"label":"sRoomDecorSlots","bank":1,"address":"a4c2","size":8},{"label":"sRoomOwned","bank":1,"address":"a4ca","size":4},{"label":"sElementPrismType","bank":1,"address":"a4ce","size":1},{"label":"sPrismCartridges","bank":1,"address":"a4cf","size":2},{"label":"sRogueSpeciesGroupsEnabled","bank":1,"address":"a4d1","size":1},{"label":"sTurnRewindBuf","bank":1,"address":"a4d2","size":34},{"label":"sGameData","bank":1,"address":"a4f4","size":11},{"label":"sPlayerName","bank":1,"address":"a4f4","size":11},{"label":"sMainData","bank":1,"address":"a4ff","size":1770},{"label":"sSpriteData","bank":1,"address":"abe9","size":512},{"label":"sPartyData","bank":1,"address":"ade9","size":404},{"label":"sCurBoxData","bank":1,"address":"af7d","size":1122},{"label":"sTileAnimations","bank":1,"address":"b3df","size":1},{"label":"sCurMap","bank":1,"address":"b3e0","size":1},{"label":"sGameDataEnd","bank":1,"address":"b3e1","size":1},{"label":"sMainDataCheckSum","bank":1,"address":"b3e1","size":1},{"label":"sFinalTeamArchive","bank":1,"address":"b3e2","size":2},{"label":"sFinalTeamArchiveMagic","bank":1,"address":"b3e2","size":2},{"label":"sFinalTeamArchiveVersion","bank":1,"address":"b3e4","size":1},{"label":"sFinalTeamArchiveCount","bank":1,"address":"b3e5","size":1},{"label":"sFinalTeamArchiveNextIndex","bank":1,"address":"b3e6","size":1},{"label":"sFinalTeamArchiveLatestIndex","bank":1,"address":"b3e7","size":1},{"label":"sFinalTeamArchiveRecordChecksums","bank":1,"address":"b3e8","size":4},{"label":"sFinalTeamArchiveHeaderChecksum","bank":1,"address":"b3ec","size":1},{"label":"sFinalTeamArchiveRecords","bank":1,"address":"b3ed","size":1624},{"label":"sFinalTeamArchiveEnd","bank":1,"address":"ba45","size":600},{"label":"sProcFacilityStagingBuffer","bank":1,"address":"ba45","size":600},{"label":"sProcFacilityExitI","bank":1,"address":"bc9d","size":1},{"label":"sProcFacilityExitEdge","bank":1,"address":"bc9e","size":1},{"label":"sProcFacilityBaked","bank":1,"address":"bc9f","size":1},{"label":"sProcFacilityBossSpecies","bank":1,"address":"bca0","size":1},{"label":"sProcFacilityBossSprite","bank":1,"address":"bca1","size":1},{"label":"sProcFacilityBallXY","bank":1,"address":"bca2","size":8},{"label":"sProcFacilityBallItems","bank":1,"address":"bcaa","size":4},{"label":"sProcFacilityItemGot","bank":1,"address":"bcae","size":1},{"label":"sProcFacilitySignVariant","bank":1,"address":"bcaf","size":1},{"label":"sProcFacilityPalette","bank":1,"address":"bcb0","size":1},{"label":"sProcFacilityEntryBattleCount","bank":1,"address":"bcb1","size":1},{"label":"sProcFacilityGenScratch","bank":1,"address":"bcb2","size":81},{"label":"sProcFacilityRoomBuf","bank":1,"address":"bd03","size":240},{"label":"sBox1","bank":2,"address":"a000","size":1122},{"label":"sBox2","bank":2,"address":"a462","size":1122},{"label":"sBox3","bank":2,"address":"a8c4","size":1122},{"label":"sBox4","bank":2,"address":"ad26","size":1122},{"label":"sBox5","bank":2,"address":"b188","size":1122},{"label":"sBox6","bank":2,"address":"b5ea","size":1122},{"label":"sBank2AllBoxesChecksum","bank":2,"address":"ba4c","size":1},{"label":"sBank2IndividualBoxChecksums","bank":2,"address":"ba4d","size":6},{"label":"sFallenLog","bank":2,"address":"ba53","size":792},{"label":"sBox7","bank":3,"address":"a000","size":1122},{"label":"sBox8","bank":3,"address":"a462","size":1122},{"label":"sBox9","bank":3,"address":"a8c4","size":1122},{"label":"sBox10","bank":3,"address":"ad26","size":1122},{"label":"sBox11","bank":3,"address":"b188","size":1122},{"label":"sBox12","bank":3,"address":"b5ea","size":1122},{"label":"sBank3AllBoxesChecksum","bank":3,"address":"ba4c","size":1},{"label":"sBank3IndividualBoxChecksums","bank":3,"address":"ba4d","size":6}],"saved_wram":[{"label":"wPlayerName","block":"sPlayerName","offset":0,"size":11},{"label":"wPokedexOwned","block":"sMainData","offset":0,"size":32},{"label":"wPokedexSeen","block":"sMainData","offset":32,"size":32},{"label":"wRivalName","block":"sMainData","offset":116,"size":11},{"label":"wOptions","block":"sMainData","offset":127,"size":1},{"label":"wPlayerID","block":"sMainData","offset":130,"size":2},{"label":"wCurrentBoxNum","block":"sMainData","offset":711,"size":2},{"label":"wNumHoFTeams","block":"sMainData","offset":713,"size":1},{"label":"wGymsUsedMask","block":"sMainData","offset":1051,"size":2},{"label":"wOptions2","block":"sMainData","offset":1054,"size":1},{"label":"wOptions3","block":"sMainData","offset":1059,"size":4},{"label":"wEventFlags","block":"sMainData","offset":1145,"size":64},{"label":"wPartyCount","block":"sPartyData","offset":0,"size":1},{"label":"wPartySpecies","block":"sPartyData","offset":1,"size":7},{"label":"wBoxCount","block":"sCurBoxData","offset":0,"size":1}]},"baseline_74f82c1b":{"schema_id":null,"source":{"sym":"pokeblue_debug.sym","commit":"74f82c1b"},"header":null,"checksums":[{"name":"main","bank":1,"start":"a4f4","length":3821,"at_bank":1,"at":"b3e1","optional":false},{"name":"boxes_1_to_6","bank":2,"start":"a000","length":6732,"at_bank":2,"at":"ba4c","optional":false},{"name":"box1","bank":2,"start":"a000","length":1122,"at_bank":2,"at":"ba4d","optional":false},{"name":"box2","bank":2,"start":"a462","length":1122,"at_bank":2,"at":"ba4e","optional":false},{"name":"box3","bank":2,"start":"a8c4","length":1122,"at_bank":2,"at":"ba4f","optional":false},{"name":"box4","bank":2,"start":"ad26","length":1122,"at_bank":2,"at":"ba50","optional":false},{"name":"box5","bank":2,"start":"b188","length":1122,"at_bank":2,"at":"ba51","optional":false},{"name":"box6","bank":2,"start":"b5ea","length":1122,"at_bank":2,"at":"ba52","optional":false},{"name":"boxes_7_to_12","bank":3,"start":"a000","length":6732,"at_bank":3,"at":"ba4c","optional":false},{"name":"box7","bank":3,"start":"a000","length":1122,"at_bank":3,"at":"ba4d","optional":false},{"name":"box8","bank":3,"start":"a462","length":1122,"at_bank":3,"at":"ba4e","optional":false},{"name":"box9","bank":3,"start":"a8c4","length":1122,"at_bank":3,"at":"ba4f","optional":false},{"name":"box10","bank":3,"start":"ad26","length":1122,"at_bank":3,"at":"ba50","optional":false},{"name":"box11","bank":3,"start":"b188","length":1122,"at_bank":3,"at":"ba51","optional":false},{"name":"box12","bank":3,"start":"b5ea","length":1122,"at_bank":3,"at":"ba52","optional":false},{"name":"final_team_header","bank":1,"start":"b3e2","length":10,"at_bank":1,"at":"b3ec","optional":true},{"name":"final_team_record0","bank":1,"start":"b3ed","length":406,"at_bank":1,"at":"b3e8","optional":true},{"name":"final_team_record1","bank":1,"start":"b583","length":406,"at_bank":1,"at":"b3e9","optional":true},{"name":"final_team_record2","bank":1,"start":"b719","length":406,"at_bank":1,"at":"b3ea","optional":true},{"name":"final_team_record3","bank":1,"start":"b8af","length":406,"at_bank":1,"at":"b3eb","optional":true}],"sram":[{"label":"sSpriteBuffer0","bank":0,"address":"a000","size":392},{"label":"sSpriteBuffer1","bank":0,"address":"a188","size":392},{"label":"sSpriteBuffer2","bank":0,"address":"a310","size":648},{"label":"sHallOfFame","bank":0,"address":"a598","size":4800},{"label":"sProcCaveStagingBuffer","bank":0,"address":"b858","size":600},{"label":"sProcCemeteryMaps","bank":0,"address":"bab0","size":360},{"label":"sProcCemeteryBallX","bank":0,"address":"bc18","size":4},{"label":"sProcCemeteryBallY","bank":0,"address":"bc1c","size":4},{"label":"sProcCemeteryItem","bank":0,"address":"bc20","size":4},{"label":"sProcCemeteryReady","bank":0,"address":"bc24","size":1},{"label":"sProcCemeteryItemGot","bank":0,"address":"bc25","size":1},{"label":"sProcCemeteryUsedPrefabs","bank":0,"address":"bc26","size":2},{"label":"sProcCemeteryBossSpecies","bank":0,"address":"bc28","size":1},{"label":"sProcCemeteryBossMove","bank":0,"address":"bc29","size":1},{"label":"sProcCaveStagingEntranceY","bank":0,"address":"bc2a","size":1},{"label":"sProcCaveStagingEntranceX","bank":0,"address":"bc2b","size":1},{"label":"sProcCaveStagingExitY","bank":0,"address":"bc2c","size":1},{"label":"sProcCaveStagingExitX","bank":0,"address":"bc2d","size":1},{"label":"sProcCaveStagingBossSprite","bank":0,"address":"bc2e","size":1},{"label":"sProcCaveStagingLadderID","bank":0,"address":"bc2f","size":1},{"label":"sProcCaveStagingLadderOffset","bank":0,"address":"bc30","size":1},{"label":"sProcCaveSignVariant","bank":0,"address":"bc31","size":1},{"label":"sProcCaveEntranceWarpID","bank":0,"address":"bc32","size":1},{"label":"sProcCaveBallsStaged","bank":0,"address":"bc33","size":1},{"label":"sProcCaveBallXY","bank":0,"address":"bc34","size":8},{"label":"sProcCaveBallItems","bank":0,"address":"bc3c","size":4},{"label":"sProcCaveBaked","bank":0,"address":"bc40","size":1},{"label":"sProcForestStagingBuffer","bank":0,"address":"bc41","size":600},{"label":"sProcForestExitI","bank":0,"address":"be99","size":1},{"label":"sProcForestExitEdge","bank":0,"address":"be9a","size":1},{"label":"sProcForestRiverSide","bank":0,"address":"be9b","size":1},{"label":"sProcForestBaked","bank":0,"address":"be9c","size":1},{"label":"sProcForestBossSpecies","bank":0,"address":"be9d","size":1},{"label":"sProcForestBossSprite","bank":0,"address":"be9e","size":1},{"label":"sProcForestBallXY","bank":0,"address":"be9f","size":8},{"label":"sProcForestBallItems","bank":0,"address":"bea7","size":4},{"label":"sProcForestItemGot","bank":0,"address":"beab","size":1},{"label":"sProcForestSignVariant","bank":0,"address":"beac","size":1},{"label":"sProcForestAlgoForce","bank":0,"address":"bead","size":1},{"label":"sProcForestGenScratch","bank":0,"address":"beae","size":81},{"label":"sProcCavePalette","bank":0,"address":"beff","size":1},{"label":"sProcForestPalette","bank":0,"address":"bf00","size":1},{"label":"sProcCemeteryPalette","bank":0,"address":"bf01","size":1},{"label":"sStageEventHideoutX","bank":0,"address":"bf02","size":1},{"label":"sStageEventHideoutY","bank":0,"address":"bf03","size":1},{"label":"sStageEventHideoutAltX","bank":0,"address":"bf04","size":1},{"label":"sStageEventHideoutAltY","bank":0,"address":"bf05","size":1},{"label":"sStageEventSprite6","bank":0,"address":"bf06","size":1},{"label":"sStageEventSprite7","bank":0,"address":"bf07","size":1},{"label":"sStageEventHideoutFloor","bank":0,"address":"bf08","size":1},{"label":"sStolenKind","bank":1,"address":"a000","size":1},{"label":"sStolenRecord","bank":1,"address":"a000","size":1},{"label":"sStolenItem","bank":1,"address":"a001","size":1},{"label":"sStolenBoxMon","bank":1,"address":"a002","size":33},{"label":"sStolenNickname","bank":1,"address":"a023","size":11},{"label":"sStolenOTName","bank":1,"address":"a02e","size":11},{"label":"sStolenRecordEnd","bank":1,"address":"a039","size":951},{"label":"sRoomOwnedExt","bank":1,"address":"a3f0","size":4},{"label":"sDebugFight2Spec","bank":1,"address":"a3f4","size":1},{"label":"sDebugFight2SpecMagic","bank":1,"address":"a3f4","size":1},{"label":"sDebugFight2PlayerCount","bank":1,"address":"a3f5","size":1},{"label":"sDebugFight2EnemyCount","bank":1,"address":"a3f6","size":1},{"label":"sDebugFight2TrainerClass","bank":1,"address":"a3f7","size":1},{"label":"sDebugFight2AITier","bank":1,"address":"a3f8","size":1},{"label":"sDebugFight2Mons","bank":1,"address":"a3f9","size":72},{"label":"sDebugFight2SpecEnd","bank":1,"address":"a441","size":112},{"label":"sFusionDiagBuf","bank":1,"address":"a441","size":112},{"label":"sTMBitfield","bank":1,"address":"a4b1","size":7},{"label":"sKeyItemsBitfield","bank":1,"address":"a4b8","size":4},{"label":"sKeyItemTiers","bank":1,"address":"a4bc","size":4},{"label":"sRoomFurniture","bank":1,"address":"a4c0","size":2},{"label":"sRoomDecorSlots","bank":1,"address":"a4c2","size":8},{"label":"sRoomOwned","bank":1,"address":"a4ca","size":4},{"label":"sElementPrismType","bank":1,"address":"a4ce","size":1},{"label":"sPrismCartridges","bank":1,"address":"a4cf","size":2},{"label":"sRogueSpeciesGroupsEnabled","bank":1,"address":"a4d1","size":1},{"label":"sTurnRewindBuf","bank":1,"address":"a4d2","size":34},{"label":"sGameData","bank":1,"address":"a4f4","size":11},{"label":"sPlayerName","bank":1,"address":"a4f4","size":11},{"label":"sMainData","bank":1,"address":"a4ff","size":1770},{"label":"sSpriteData","bank":1,"address":"abe9","size":512},{"label":"sPartyData","bank":1,"address":"ade9","size":404},{"label":"sCurBoxData","bank":1,"address":"af7d","size":1122},{"label":"sTileAnimations","bank":1,"address":"b3df","size":1},{"label":"sCurMap","bank":1,"address":"b3e0","size":1},{"label":"sGameDataEnd","bank":1,"address":"b3e1","size":1},{"label":"sMainDataCheckSum","bank":1,"address":"b3e1","size":1},{"label":"sFinalTeamArchive","bank":1,"address":"b3e2","size":2},{"label":"sFinalTeamArchiveMagic","bank":1,"address":"b3e2","size":2},{"label":"sFinalTeamArchiveVersion","bank":1,"address":"b3e4","size":1},{"label":"sFinalTeamArchiveCount","bank":1,"address":"b3e5","size":1},{"label":"sFinalTeamArchiveNextIndex","bank":1,"address":"b3e6","size":1},{"label":"sFinalTeamArchiveLatestIndex","bank":1,"address":"b3e7","size":1},{"label":"sFinalTeamArchiveRecordChecksums","bank":1,"address":"b3e8","size":4},{"label":"sFinalTeamArchiveHeaderChecksum","bank":1,"address":"b3ec","size":1},{"label":"sFinalTeamArchiveRecords","bank":1,"address":"b3ed","size":1624},{"label":"sFinalTeamArchiveEnd","bank":1,"address":"ba45","size":600},{"label":"sProcFacilityStagingBuffer","bank":1,"address":"ba45","size":600},{"label":"sProcFacilityExitI","bank":1,"address":"bc9d","size":1},{"label":"sProcFacilityExitEdge","bank":1,"address":"bc9e","size":1},{"label":"sProcFacilityBaked","bank":1,"address":"bc9f","size":1},{"label":"sProcFacilityBossSpecies","bank":1,"address":"bca0","size":1},{"label":"sProcFacilityBossSprite","bank":1,"address":"bca1","size":1},{"label":"sProcFacilityBallXY","bank":1,"address":"bca2","size":8},{"label":"sProcFacilityBallItems","bank":1,"address":"bcaa","size":4},{"label":"sProcFacilityItemGot","bank":1,"address":"bcae","size":1},{"label":"sProcFacilitySignVariant","bank":1,"address":"bcaf","size":1},{"label":"sProcFacilityPalette","bank":1,"address":"bcb0","size":1},{"label":"sProcFacilityEntryBattleCount","bank":1,"address":"bcb1","size":1},{"label":"sProcFacilityGenScratch","bank":1,"address":"bcb2","size":81},{"label":"sProcFacilityRoomBuf","bank":1,"address":"bd03","size":240},{"label":"sBox1","bank":2,"address":"a000","size":1122},{"label":"sBox2","bank":2,"address":"a462","size":1122},{"label":"sBox3","bank":2,"address":"a8c4","size":1122},{"label":"sBox4","bank":2,"address":"ad26","size":1122},{"label":"sBox5","bank":2,"address":"b188","size":1122},{"label":"sBox6","bank":2,"address":"b5ea","size":1122},{"label":"sBank2AllBoxesChecksum","bank":2,"address":"ba4c","size":1},{"label":"sBank2IndividualBoxChecksums","bank":2,"address":"ba4d","size":6},{"label":"sFallenLog","bank":2,"address":"ba53","size":792},{"label":"sBox7","bank":3,"address":"a000","size":1122},{"label":"sBox8","bank":3,"address":"a462","size":1122},{"label":"sBox9","bank":3,"address":"a8c4","size":1122},{"label":"sBox10","bank":3,"address":"ad26","size":1122},{"label":"sBox11","bank":3,"address":"b188","size":1122},{"label":"sBox12","bank":3,"address":"b5ea","size":1122},{"label":"sBank3AllBoxesChecksum","bank":3,"address":"ba4c","size":1},{"label":"sBank3IndividualBoxChecksums","bank":3,"address":"ba4d","size":6}],"saved_wram":[{"label":"wPlayerName","block":"sPlayerName","offset":0,"size":11},{"label":"wPokedexOwned","block":"sMainData","offset":0,"size":32},{"label":"wPokedexSeen","block":"sMainData","offset":32,"size":32},{"label":"wRivalName","block":"sMainData","offset":116,"size":11},{"label":"wOptions","block":"sMainData","offset":127,"size":1},{"label":"wPlayerID","block":"sMainData","offset":130,"size":2},{"label":"wCurrentBoxNum","block":"sMainData","offset":711,"size":2},{"label":"wNumHoFTeams","block":"sMainData","offset":713,"size":1},{"label":"wGymsUsedMask","block":"sMainData","offset":1051,"size":2},{"label":"wOptions2","block":"sMainData","offset":1054,"size":1},{"label":"wOptions3","block":"sMainData","offset":1059,"size":4},{"label":"wEventFlags","block":"sMainData","offset":1145,"size":64},{"label":"wPartyCount","block":"sPartyData","offset":0,"size":1},{"label":"wPartySpecies","block":"sPartyData","offset":1,"size":7},{"label":"wBoxCount","block":"sCurBoxData","offset":0,"size":1}]}},"sources":[{"id":"baseline_74f82c1b","label":"2026-10-01 74f82c1b","schema":"baseline_74f82c1b","rom_sha256":["e6a97a608c72d87550771529b568260af5782b64fe174d0fe6087b79ef6e9707"]}],"migrations":[{"from":"baseline_74f82c1b","to":"1","steps":["tag"]}],"recovery":null};
})(typeof self !== "undefined" ? self : this);
