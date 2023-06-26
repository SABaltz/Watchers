import React from 'react'
import Box from "@mui/material/Box";

let dentist1 = require('../static/dentist1.jpg')
export default function HomePage({context}) {
    return (
        <>
            <Box
                sx={{
                    backgroundImage: 'url(' + dentist1 + ')',
                    backgroundRepeat: "no-repeat",
                    backgroundPosition: 'center',
                    backgroundSize: 'cover',
                    width: '100vw',
                    height: '100vh'
                }}
            >

            </Box>
            <div>test</div>
        </>
    )
}
