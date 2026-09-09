# EVERYONE IS HERE, a slice, in its maintainer's sentences (2026-09-08). bin/counter seat assays/sheet.feature
model Sheet

a Role is one of: couple, vendor, helper
# Abe, 2026-09-08: a vendor is a helper who gets paid — held in assays/eih.held until the grammar can say it
a Page is one of: floorPlan, guestList, samePage, invoices, budget, guests, site, team, dayOf, tasks
a Ask is one of: guests, sheet, timeline, bachelor

the couple sees: every Page
the vendor sees: floorPlan, samePage, invoices, team, dayOf, tasks
the helper sees: floorPlan, guestList, samePage, team, dayOf, tasks

the couple edits: every Page
the vendor edits: invoices, dayOf, tasks
the helper edits: floorPlan, guestList, dayOf, tasks

a Room has: guests (a list of numbers), delivered (a list of numbers), timeline (a list of numbers), bachelor (a list of numbers)
the room reads: guests as guests, sheet as delivered, timeline as timeline, bachelor as bachelor

the couple hears: guests, sheet, timeline
the caterer hears: timeline, sheet
the best man hears: timeline, bachelor

a Room may: withBachelor (bachelor becomes the argument)
a Room may: withGuests (guests becomes the argument)
a Room may: withTime (timeline gets the argument first)

wall: withBachelor changes nothing the couple hears
wall: withBachelor changes nothing the caterer hears
wall: withGuests changes nothing the caterer hears
wall: withGuests changes nothing the best man hears

given demo is a Room with guests [2, 3, 1], delivered [], timeline [10, 11, 12], bachelor [42]
when demo withBachelor [43] is newBach
then the caterer hears [[10, 11, 12], []] in demo
then the best man hears [[10, 11, 12], [43]] in newBach
then the couple hears [[2, 3, 1], [], [10, 11, 12]] in newBach
