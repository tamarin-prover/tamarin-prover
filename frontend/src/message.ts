export type BroadcastMessage = {
    type: BroadcastMessageType,
    payload?: string | null
}

export type BroadcastMessageType = "close-popup" | "popup-closed" | "host-dotsrc-changed" 