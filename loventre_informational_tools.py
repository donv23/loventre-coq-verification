#!/usr/bin/env python3
# -*- coding: utf-8 -*-

##############################################################
#  LOVENTRE INFORMATIONAL TOOLS v5.3-STABLE
#  (3-input potential/inertia consistent with Geometry tab)
##############################################################

def informational_potential(kappa, entropy, V0):
    """
    Potenziale informazionale Loventre:
       P = (kappa + entropy) / (1 + V0)

    - kappa, entropy, V0: numeri float
    - ritorna float
    """
    try:
        return (float(kappa) + float(entropy)) / (1.0 + float(V0))
    except Exception:
        return None


def informational_inertia(kappa, entropy, V0):
    """
    Inerzia informazionale Loventre:
       I = abs(kappa - entropy) * V0

    - ritorna float
    """
    try:
        return abs(float(kappa) - float(entropy)) * float(V0)
    except Exception:
        return None


##############################################################
#  Utility: stampa tabella
##############################################################
def informational_print_table(headers, rows):
    widths = [len(h) for h in headers]
    for row in rows:
        for i,val in enumerate(row):
            widths[i] = max(widths[i], len(str(val)))

    header_line = " | ".join(h.ljust(widths[i]) for i,h in enumerate(headers))
    sep_line    = "-+-".join("-"*widths[i] for i,_ in enumerate(headers))
    print(header_line)
    print(sep_line)

    for row in rows:
        print(" | ".join(str(row[i]).ljust(widths[i]) for i,_ in enumerate(headers)))

